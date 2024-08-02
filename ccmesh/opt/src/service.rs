use crate::opt::mesh_client::MeshClient;
use crate::opt::mesh_server::{Mesh, MeshServer};
use crate::opt::{
    CleanUpRequest, ClientWriteRequest, ClientWriteResponse, HealthCheckRequest,
    HealthCheckResponse, ServerReadRequest, ServerReadResponse,
};
use crate::opt::{ClientReadRequest, ClientReadResponse};
use crate::opt::{PrepareRequest, PrepareResponse};
use crate::utils::*;
use array_macro::array;
use dashmap::DashMap;
use fxhash::FxBuildHasher;
use hz_causal::*;
use hz_config::*;
use hz_redis::helper::{create_connection, redis_get, REDIS_CODING};
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

pub struct OptService {
    pub id: usize,
    pub cut: RHandle,
    pub redis: Sender<M>,
    pub tmp: DashMap<String, HashMap<String, M>, FxBuildHasher>,
    counter: AtomicI32,
}

impl OptService {
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
impl Mesh for OptService {
    async fn health_check(
        &self,
        _request: Request<HealthCheckRequest>,
    ) -> Result<Response<HealthCheckResponse>, Status> {
        Ok(Response::new(HealthCheckResponse {
            status: "OK".to_string(),
        }))
    }

    async fn prepare(
        &self,
        request: Request<PrepareRequest>,
    ) -> Result<Response<PrepareResponse>, Status> {
        let req = request.into_inner();
        let mut su: HashMap<K, VC> = serde_json::from_str(&req.su).unwrap();
        let mut ru: HashMap<K, VC> = serde_json::from_str(&req.ru).unwrap();
        if !self.tmp.contains_key(&req.id) {
            self.tmp.insert(req.id.clone(), HashMap::default());
        }
        let mut tmp_k = self.tmp.get_mut(&req.id).unwrap();
        let mut remote: HashSet<K> = HashSet::default();
        let read_guard = self.cut.guard();
        // let mut todo = HashMap::default();
        // let mut tmp_local = HashMap::default();
        for k in req.keys.iter() {
            let k = k.clone();
            let b1 = read_guard.contains_key(&k);
            let b2 = su.contains_key(&k);
            if !b1 && b2 {
                remote.insert(k);
            } else if !b1 && !b2 {
                panic!("never happen");
                // let mut conn = create_connection();
                // let m: Option<M> = redis_get(&mut conn, &k);
                // if let Some(m) = m {
                //     let mut t = HashMap::default();
                //     t.insert(k, vec![m.clone()]);
                //     let guard = self.cut.guard();
                //     let covered = is_covered2(m, &mut t, &guard, &mut conn);
                //     if !covered {
                //         return Ok(Response::new(PrepareResponse {
                //             abort: true,
                //             su: "".to_string(),
                //             ru: "".to_string(),
                //         }));
                //     }
                //     for (k_, metas) in t.iter() {
                //         let mut meta = metas[0].clone();
                //         for m_ in metas {
                //             meta.merge_into(m_);
                //         }
                //         todo.insert_or_merge(k_.clone(), meta);
                //     }
                // } else {
                //     return Ok(Response::new(PrepareResponse {
                //         abort: true,
                //         su: "".to_string(),
                //         ru: "".to_string(),
                //     }));
                // }
            }
        }
        let mut rlocal: HashMap<K, M> = HashMap::default();
        for k in req.keys {
            if let Some(m) = read_guard.get(&k) {
                rlocal.insert(k, m.no_deps());
            }
        }
        for (k, vc) in su.iter() {
            if let Some(mm) = rlocal.get(k) {
                if !(*vc <= mm.vc) {
                    remote.insert(k.clone());
                }
            }
        }
        let mut abort = false;
        let mut s_map: HashMap<K, HashMap<K, M>> = HashMap::default();
        let mut to_remove: Vec<String> = Vec::new();
        'outer: for (k, _) in rlocal.iter() {
            let si = retrieve_cut(&read_guard, k);
            for (kk, mi) in si.iter() {
                if ru.contains_key(kk) && !(mi.vc <= ru[kk]) {
                    if !su.contains_key(k) {
                        abort = true;
                        break 'outer;
                    } else {
                        remote.insert(k.clone());
                        to_remove.push(k.clone());
                    }
                }
            }
            s_map.insert(k.clone(), si.clone());
        }
        for k in to_remove {
            rlocal.remove(&k);
        }
        if abort {
            return Ok(Response::new(PrepareResponse {
                abort: true,
                su: "".to_string(),
                ru: "".to_string(),
            }));
        }
        let mut sd = HashMap::default();
        for (k, _) in rlocal.iter() {
            let s_map_k = s_map.get(k).unwrap();
            sd.merge_into(s_map_k);
        }
        tmp_k.merge_into(&sd);
        // tmp_k.merge_into(&todo);
        // su.merge_into(&sd);
        for (k, m) in sd {
            su.insert_or_merge(k, m.vc);
        }

        let mut rd = rlocal.clone();
        if remote.is_empty() || self.id == req.upstream as usize {
            if !remote.is_empty() && self.id == req.upstream as usize {
                for k in remote.iter() {
                    rd.insert_or_merge(k.clone(), tmp_k.get(k).unwrap().no_deps());
                }
            }
            tmp_k.merge_into(&rd);
            // ru.merge_into(&rd);
            for (k, m) in rd {
                ru.insert_or_merge(k, m.vc);
            }
            // for (k, v) in tmp_k.iter() {
            //     println!("{}: {} -> {}", self.id, k, v.value);
            // }
            return Ok(Response::new(PrepareResponse {
                abort: false,
                su: serde_json::to_string(&su).unwrap(),
                ru: serde_json::to_string(&ru).unwrap(),
            }));
        } else {
            tmp_k.merge_into(&rd);
            drop(tmp_k);
            let mut client = rpc_client(req.upstream as usize);
            // let upstream_ip = PEERS[req.upstream as usize];
            // let mut client = MeshClient::connect(format!("http://{upstream_ip}"))
            //     .await
            //     .unwrap();
            let resp = client
                .server_read(ServerReadRequest {
                    id: req.id.clone(),
                    keys: remote.into_iter().collect(),
                    owner: req.upstream,
                })
                .await
                .unwrap()
                .into_inner();
            // for k in remote.iter() {
            //     rd.insert_or_merge(k.clone(), tmp_k.get(k).unwrap().clone());
            // }
            let km: HashMap<K, M> = serde_json::from_str(&resp.res).unwrap();
            let mut tmp_k = self.tmp.get_mut(&req.id).unwrap();
            tmp_k.merge_into(&km);
            rd.merge_into(&km);
            // ru.merge_into(&rd);
            for (k, m) in rd {
                ru.insert_or_merge(k, m.vc);
            }
            // for (k, v) in tmp_k.iter() {
            //     println!("{}: {} -> {}", self.id, k, v.value);
            // }
            return Ok(Response::new(PrepareResponse {
                abort: false,
                su: serde_json::to_string(&su).unwrap(),
                ru: serde_json::to_string(&ru).unwrap(),
            }));
        }
    }

    async fn client_read(
        &self,
        request: Request<ClientReadRequest>,
    ) -> Result<Response<ClientReadResponse>, Status> {
        let req = request.into_inner();
        let mut m: M = M::new(req.key.clone(), "".into());
        if let Some(local) = self.tmp.get(&req.id) {
            if let Some(mm) = local.get(&req.key) {
                m = mm.no_deps();
            }
        }
        Ok(Response::new(ClientReadResponse {
            value: m.value.clone(),
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
        if DURABLE {
            self.redis
                .send(M {
                    key: req.key.clone(),
                    value: req.value.clone(),
                    vc: max_vc.clone(),
                    deps: deps.clone(),
                })
                .await
                .unwrap();
            // hz_redis::helper::REDIS_R.with(|conn| {
            //     let _res: () = conn.borrow_mut().publish("NEW", req.key).unwrap();
            // });
        }
        Ok(Response::new(ClientWriteResponse {
            vc: serde_json::to_string(&max_vc).unwrap(),
        }))
    }

    async fn server_read(
        &self,
        request: Request<ServerReadRequest>,
    ) -> Result<Response<ServerReadResponse>, Status> {
        let req = request.into_inner();
        let tmp_k = self.tmp.get(&req.id).unwrap();
        let mut res: HashMap<K, M> = HashMap::default();
        for k in req.keys.iter() {
            let m = tmp_k.get(k).unwrap();
            res.insert(k.clone(), m.clone());
        }
        Ok(Response::new(ServerReadResponse {
            res: serde_json::to_string(&res).unwrap(),
        }))
    }

    async fn clean_up(&self, request: Request<CleanUpRequest>) -> Result<Response<()>, Status> {
        let req = request.into_inner();
        self.tmp.remove(&req.id);
        Ok(Response::new(()))
    }
}

pub async fn run(id: usize) {
    let opt_service = OptService::new(id);
    std::println!("Server listening on http://{}", PEERS[id]);

    Server::builder()
        .add_service(MeshServer::new(opt_service))
        .serve("0.0.0.0:18080".parse().unwrap())
        .await
        .unwrap();
}
