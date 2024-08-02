use crate::cb::mesh_client::MeshClient;
use crate::cb::mesh_server::{Mesh, MeshServer};
use crate::cb::{ClientReadRequest, ClientReadResponse};
use crate::cb::{ServerReadRequest, ServerReadResponse};
use crate::cb::{ClientWriteRequest, ClientWriteResponse};
use crate::cb::{HealthCheckRequest, HealthCheckResponse};
use crate::utils::*;
use array_macro::array;
use dashmap::DashMap;
use fxhash::FxBuildHasher;
use hz_causal::*;
use hz_config::*;
use hz_redis::helper::{REDIS_CODING, redis_get};
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

pub struct CbService {
    pub id: usize,
    pub cut: RHandle,
    pub redis: Sender<M>,
    counter: AtomicI32,
    to_resolver: tokio::sync::mpsc::Sender<HashSet<String>>,
}

impl CbService {
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
        let (to_resolver, from_bg) = tokio::sync::mpsc::channel(10000);
        let builder = std::thread::Builder::new().name("hz-server-bg".into());
        builder
            .spawn(move || {
                background(map_w, from_bg);
            })
            .unwrap();
        Self {
            id,
            cut: map_r,
            counter: AtomicI32::new(0),
            redis: redis_sender,
            to_resolver,
        }
    }
}

#[tonic::async_trait]
impl Mesh for CbService {
    async fn health_check(
        &self,
        _request: Request<HealthCheckRequest>,
    ) -> Result<Response<HealthCheckResponse>, Status> {
        Ok(Response::new(HealthCheckResponse {
            status: "OK".to_string(),
        }))
    }

    async fn server_read(
        &self,
        request: Request<ServerReadRequest>,
    ) -> Result<Response<ServerReadResponse>, Status> {
        let req = request.into_inner();
        let m = self.cut.guard().get(&req.key).unwrap().clone();
        return Ok(Response::new(ServerReadResponse {
            value: m.value.clone(),
            vc: serde_json::to_string(&m.vc).unwrap(),
        }));
    }

    async fn client_read(
        &self,
        request: Request<ClientReadRequest>,
    ) -> Result<Response<ClientReadResponse>, Status> {
        let req = request.into_inner();
        let m = self.cut.guard().get(&req.key).unwrap().clone();
        let deps: HashMap<String, VC> = serde_json::from_str(&req.deps).unwrap();
        let mut to_send: HashSet<String> = deps.keys().cloned().collect();
        // to_send.insert(req.key.clone());
        self.to_resolver
            .send(to_send)
            .await
            .unwrap();
        if deps.contains_key(&req.key) {
            let vc = deps.get(&req.key).unwrap();
            if !(vc <= &m.vc) {
                // let mm: Option<M> = hz_redis::helper::REDIS_R.with(|conn| {
                //     redis_get(&mut conn.borrow_mut(), req.key)
                // });
                let mut client = rpc_client(req.upstream as usize);
                let mm = client
                    .server_read(ServerReadRequest {
                        key: req.key.clone(),
                    })
                    .await
                    .unwrap()
                    .into_inner();
                return Ok(Response::new(ClientReadResponse {
                    value: mm.value,
                    vc: serde_json::to_string(&m.vc).unwrap(),
                }));
            }
        }
        return Ok(Response::new(ClientReadResponse {
            value: m.value.clone(),
            vc: serde_json::to_string(&m.vc).unwrap(),
        }));
    }

    async fn client_write(
        &self,
        request: Request<ClientWriteRequest>,
    ) -> Result<Response<ClientWriteResponse>, Status> {
        let req = request.into_inner();
        let mut max_vc = VC::default();
        let deps: HashMap<String, VC> = serde_json::from_str(&req.deps).unwrap();
        let mut to_send: HashSet<String> = deps.keys().cloned().collect();
        // to_send.insert(req.key.clone());
        self.to_resolver
            .send(to_send)
            .await
            .unwrap();
        for (_, vc) in deps.iter() {
            max_vc.merge_into(vc);
        }
        let previous = self.counter.fetch_add(1, Ordering::SeqCst);
        max_vc.0[self.id] = previous + 1;
        let m = M {
            key: req.key.clone(),
            value: req.value,
            vc: max_vc.clone(),
            deps,
        };
        if DURABLE {
            self.redis.send(m).await.unwrap();
            // hz_redis::helper::REDIS_R.with(|conn| {
            //     let _res: () = conn.borrow_mut().publish("NEW", req.key).unwrap();
            // });
        }
        Ok(Response::new(ClientWriteResponse {
            vc: serde_json::to_string(&max_vc).unwrap(),
        }))
    }
}

pub async fn run(id: usize) {
    let con_service = CbService::new(id);
    println!("Server listening on http://{}", PEERS[id]);

    Server::builder()
        .add_service(MeshServer::new(con_service))
        .serve("0.0.0.0:18080".parse().unwrap())
        .await
        .unwrap();
}
