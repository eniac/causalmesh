use crate::con::mesh_client::MeshClient;
use crate::con::mesh_server::{Mesh, MeshServer};
use crate::con::CleanUpRequest;
use crate::con::Prepare2Request;
use crate::con::{ClientReadRequest, ClientReadResponse};
use crate::con::{ClientWriteRequest, ClientWriteResponse};
use crate::con::{HealthCheckRequest, HealthCheckResponse};
use crate::con::{Prepare1Request, Prepare1Response};
use crate::con::{ServerReadRequest, ServerReadResponse};
use crate::utils::*;
use array_macro::array;
use dashmap::DashMap;
use fxhash::FxBuildHasher;
use hz_causal::*;
use hz_config::*;
use hz_redis::helper::REDIS_CODING;
use hz_workload::to_populate;
use once_cell::sync::OnceCell;
use redis::Commands;
use rustc_hash::FxHashMap as HashMap;
use std::sync::atomic::{AtomicI32, Ordering};
use tokio::net::TcpStream;
use tokio::sync::mpsc::{self, Sender};
use tonic::{transport::Server, Request, Response, Status};

pub static CLIENTS: [OnceCell<MeshClient<tonic::transport::Channel>>; T] =
    array![_ => OnceCell::new(); T];

pub fn rpc_client(idx: usize) -> MeshClient<tonic::transport::Channel> {
    CLIENTS[idx].get().unwrap().clone()
}

pub struct ConService {
    pub id: usize,
    pub cut: RHandle,
    pub tmp: DashMap<String, HashMap<String, M>, FxBuildHasher>,
    pub redis: Sender<M>,
    counter: AtomicI32,
}

impl ConService {
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
            tmp: Default::default(),
            counter: AtomicI32::new(0),
            redis: redis_sender,
        }
    }
}

#[tonic::async_trait]
impl Mesh for ConService {
    async fn health_check(
        &self,
        _request: Request<HealthCheckRequest>,
    ) -> Result<Response<HealthCheckResponse>, Status> {
        Ok(Response::new(HealthCheckResponse {
            status: "OK".to_string(),
        }))
    }

    async fn prepare1(
        &self,
        request: Request<Prepare1Request>,
    ) -> Result<Response<Prepare1Response>, Status> {
        let req = request.into_inner();
        let read_guard = self.cut.guard();
        let metaset = create_snapshot(&read_guard, &req.ri, &req.rdag);
        let metaset_str = serde_json::to_string(&metaset).unwrap();
        self.tmp.insert(req.id, metaset);
        Ok(Response::new(Prepare1Response {
            metaset: metaset_str,
        }))
    }

    async fn prepare2(&self, request: Request<Prepare2Request>) -> Result<Response<()>, Status> {
        let req = request.into_inner();
        let rremote: HashMap<K, Vec<usize>> = serde_json::from_str(&req.rremote).unwrap();
        let mut rev_remote = HashMap::<usize, Vec<K>>::default();
        for (k, owners) in &rremote {
            for owner in owners {
                rev_remote
                    .entry(*owner)
                    .or_insert_with(Vec::new)
                    .push(k.clone());
            }
        }
        let mut from_remote: HashMap<K, M> = HashMap::default();
        for (owner, ks) in rev_remote.into_iter() {
            assert!(owner != self.id);
            let mut client = rpc_client(owner);
            // let server_ip = PEERS[owner];
            // let mut client = MeshClient::connect(format!("http://{server_ip}"))
            //     .await
            //     .unwrap();
            let res = client
                .server_read(ServerReadRequest {
                    id: req.id.clone(),
                    ks,
                })
                .await
                .unwrap();
            let res: HashMap<K, M> = serde_json::from_str(&res.into_inner().metaset).unwrap();
            from_remote.merge_into(&res);
        }
        self.tmp.get_mut(&req.id).unwrap().merge_into(&from_remote);
        Ok(Response::new(()))
    }

    async fn server_read(
        &self,
        request: Request<ServerReadRequest>,
    ) -> Result<Response<ServerReadResponse>, Status> {
        let req = request.into_inner();
        let mut metaset: HashMap<K, M> = HashMap::default();
        {
            let client_tmp = self.tmp.get(&req.id).unwrap();
            for k in req.ks.into_iter() {
                let m = client_tmp.get(&k).unwrap();
                metaset.insert_or_merge(k, m.no_deps());
            }
        }
        Ok(Response::new(ServerReadResponse {
            metaset: serde_json::to_string(&metaset).unwrap(),
        }))
    }

    async fn clean_up(&self, request: Request<CleanUpRequest>) -> Result<Response<()>, Status> {
        let req = request.into_inner();
        self.tmp.remove(&req.id).unwrap();
        Ok(Response::new(()))
    }

    async fn client_read(
        &self,
        request: Request<ClientReadRequest>,
    ) -> Result<Response<ClientReadResponse>, Status> {
        let req = request.into_inner();
        let mut m: M = M::new(req.key.clone(), "".into());
        {
            let client_tmp = self.tmp.get(&req.id);
            if let Some(client_tmp) = client_tmp {
                if let Some(mm) = client_tmp.get(&req.key) {
                    m = mm.no_deps();
                }
            }
        }
        Ok(Response::new(ClientReadResponse {
            value: m.value,
            vc: serde_json::to_string(&m.vc).unwrap(),
        }))
    }

    async fn client_write(
        &self,
        request: Request<ClientWriteRequest>,
    ) -> Result<Response<ClientWriteResponse>, Status> {
        if rand::random::<u64>() % 1000 == 0 {
            let tmp_l: Vec<u8> = bincode::serialize(&self.tmp.clone()).unwrap();
            // println!("tmp_l:   {}", tmp_l.len());
            let mut size = 0;
            for (k, m) in self.cut.guard().iter() {
                size += m.deps.len() * 11;
            }
            // println!("deps_size:   {}", size);
        }
        let req = request.into_inner();
        let mut max_vc = VC::default();
        let deps: HashMap<String, VC> = serde_json::from_str(&req.deps).unwrap();
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
    let con_service = ConService::new(id);
    println!("Server listening on http://{}", PEERS[id]);

    Server::builder()
        .add_service(MeshServer::new(con_service))
        .serve("0.0.0.0:18080".parse().unwrap())
        .await
        .unwrap();
}
