use crate::faas::mesh_client::MeshClient;
use crate::faas::mesh_server::{Mesh, MeshServer};
use crate::faas::{
    ClientWriteRequest, ClientWriteResponse, HealthCheckRequest,
    HealthCheckResponse,
};
use crate::faas::{ClientReadRequest, ClientReadResponse};
use crate::utils::*;
use array_macro::array;
use dashmap::DashMap;
use fxhash::FxBuildHasher;
use hz_causal::*;
use hz_config::*;
use hz_redis::helper::{create_connection, redis_get, redis_set, REDIS_CODING};
use hz_workload::to_populate;
use once_cell::sync::OnceCell;
use redis::Commands;
use rustc_hash::FxHashMap as HashMap;
use rustc_hash::FxHashSet as HashSet;
use std::sync::atomic::{AtomicI32, Ordering};
use tokio::net::TcpStream;
use tokio::sync::mpsc::{self, Sender};
use tonic::{transport::Server, Request, Response, Status};

pub static CLIENTS: [OnceCell<MeshClient<tonic::transport::Channel>>; T] =
    array![_ => OnceCell::new(); T];

pub fn rpc_client(idx: usize) -> MeshClient<tonic::transport::Channel> {
    CLIENTS[idx].get().unwrap().clone()
}

pub struct FaasService {
    pub id: usize,
    pub cut: RHandle,
    pub redis: Sender<M>,
    counter: AtomicI32,
}

impl FaasService {
    pub fn new(id: usize) -> Self {
        let (mut map_w, map_r) = flashmap::new();
        // let cut = DashMap::default();
        {
            let mut guard = map_w.guard();
            if !MEDIA {
                for i in 0..MAXKEY {
                    let key = format!("{}", i);
                    let value = format!("{:0>8}", i);
                    let m: M = M::new(key, value);
                    guard.insert(format!("{}", i), m);
                }
            }
            if MEDIA {
                for (k, v) in to_populate().into_iter() {
                    let m: M = M::new(k.clone(), v);
                    guard.insert(k, m);
                }
            }
        }
        // assert_eq!(map_r.guard().get("1").unwrap().value, "1");
        let (redis_sender, mut redis_receiver) = mpsc::channel(100);
        if DURABLE {
            tokio::spawn(async move {
                let stream = TcpStream::connect(format!("{REDISIP}:28080"))
                    .await
                    .unwrap();
                let mut conn = RedisConn::new(0, stream, REDIS_CODING);
                if id == 0 {
                    if !MEDIA {
                        for i in 0..MAXKEY {
                            let key = format!("{}", i);
                            let value = format!("{:0>8}", i);
                            let m: M = M::new(key, value);
                            conn.write_frame(&m).await.unwrap();
                        }
                    }
                    if MEDIA {
                        for (k, v) in to_populate().into_iter() {
                            let m: M = M::new(k, v);
                            conn.write_frame(&m).await.unwrap();
                        }
                    }
                    conn.flush().await.unwrap();
                }
                while let Some(m) = redis_receiver.recv().await {
                    conn.write_frame_and_flush(&m).await.unwrap();
                }
            });
        }
        for idx in 0..T {
            if idx == id {
                continue;
            }
            let addr = format!("http://{}", PEERS[idx]);
            let channel = tonic::transport::Channel::from_shared(addr)
                .unwrap()
                .connect_lazy();
            CLIENTS[idx].set(MeshClient::new(channel)).unwrap();
        }
        // std::thread::spawn(move || background(map_w));
        let builder = std::thread::Builder::new().name("hz-server-bg".into());
        builder
            .spawn(move || {
                background(map_w);
            })
            .unwrap();
        Self {
            id,
            cut: map_r,
            counter: AtomicI32::new(0),
            redis: redis_sender,
        }
    }
}

#[tonic::async_trait]
impl Mesh for FaasService {
    async fn health_check(
        &self,
        _request: Request<HealthCheckRequest>,
    ) -> Result<Response<HealthCheckResponse>, Status> {
        Ok(Response::new(HealthCheckResponse {
            status: "OK".to_string(),
        }))
    }

    async fn client_read(
        &self,
        request: Request<ClientReadRequest>,
    ) -> Result<Response<ClientReadResponse>, Status> {
        let req = request.into_inner();
        
        let low = req.low;
        let high = req.high;

        let read_guard = self.cut.guard();
        let m = read_guard.get(&req.key).unwrap();
        if m.vc.0[0] >= low && m.vc.0[0] <= high {
            return Ok(Response::new(ClientReadResponse {
                value: m.value.clone(),
                low,
                high,
                abort: false,
            }));
        }

        Ok(Response::new(ClientReadResponse {
            value: "".to_string(),
            low,
            high,
            abort: true,
        }))
    }

    async fn client_write(
        &self,
        request: Request<ClientWriteRequest>,
    ) -> Result<Response<ClientWriteResponse>, Status> {
        let req = request.into_inner();
        let ts = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_millis() as i32;
        let mut vc = VC::default();
        vc.0[0] = ts;
        let m = M {
            key: req.key.clone(),
            value: req.value.clone(),
            vc,
            deps: HashMap::default(),
        };
        hz_redis::helper::REDIS_R.with(|conn| {
            let _res: () = redis_set(&mut conn.borrow_mut(), req.key.clone(), m);
            let _res: () = conn.borrow_mut().publish("NEW", req.key).unwrap();
        });
        Ok(Response::new(ClientWriteResponse {
            ts: ts.into(),
        }))
    }
}

pub async fn run(id: usize) {
    let opt_service = FaasService::new(id);
    std::println!("Server listening on http://{}", PEERS[id]);

    Server::builder()
        .add_service(MeshServer::new(opt_service))
        .serve("0.0.0.0:18080".parse().unwrap())
        .await
        .unwrap();
}
