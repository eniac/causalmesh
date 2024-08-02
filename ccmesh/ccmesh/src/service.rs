use cc_mesh::mesh_client::MeshClient;
use cc_mesh::mesh_server::{Mesh, MeshServer};
use cc_mesh::ServerWriteRequest;
use cc_mesh::{ClientReadRequest, ClientReadResponse};
use cc_mesh::{ClientWriteRequest, ClientWriteResponse};
use cc_mesh::{HealthCheckRequest, HealthCheckResponse};
use cc_mesh::{IsVisibleRequest, IsVisibleResponse};
use ringbuffer::{AllocRingBuffer, RingBuffer};
use hz_causal::*;
use hz_config::*;
use hz_redis::helper::*;
use hz_workload::to_populate;
use once_cell::sync::OnceCell;
use rustc_hash::FxHashMap as HashMap;
use rustc_hash::FxHashSet as HashSet;
use std::collections::hash_map::Entry;
use std::sync::{Mutex, MutexGuard};
use tokio::net::TcpStream;
use tokio::sync::mpsc::{self, Sender};
use tonic::{transport::Server, Request, Response, Status};
use tracing::info;
pub mod cc_mesh {
    #![allow(clippy::derive_partial_eq_without_eq)]
    tonic::include_proto!("ccmesh");
}

pub static CLIENT: OnceCell<MeshClient<tonic::transport::Channel>> = OnceCell::new();

pub fn rpc_client() -> MeshClient<tonic::transport::Channel> {
    CLIENT.get().unwrap().clone()
}

type Black = HashMap<String, Vec<M>>;
type White = HashMap<String, M>;
type White2 = HashMap<String, AllocRingBuffer<M>>;
pub static CHEKC_BLK: bool = SCALE;
// type RPCClient = MeshClient<tonic::transport::Channel>;

#[derive(Debug)]
pub struct CCMeshService {
    pub id: usize,
    pub white: Mutex<White>,
    pub white2: Mutex<White2>,
    // TODO: use a more efficient data structure
    pub black: Mutex<Black>,
    pub vc: Mutex<VC>,
    pub next: flume::Sender<ServerWriteRequest>,
    pub redis: Sender<M>,
}

async fn proxy(receiver: flume::Receiver<ServerWriteRequest>) {
    while let Ok(req) = receiver.recv() {
        rpc_client().server_write(req).await.unwrap();
    }
}

impl CCMeshService {
    pub fn new(id: usize) -> Self {
        let mut white = White::default();
        let mut white2 = White2::default();
        let mut black = Black::default();
        if !MEDIA {
            for i in 0..MAXKEY {
                let key = format!("{}", i);
                let value = format!("{:0>8}", i);
                let m: M = M::new(key, value);
                if MV {
                    let mut buf = AllocRingBuffer::with_capacity(MV_SIZE);
                    buf.push(m);
                    white2.insert(format!("{}", i), buf);
                } else {
                    white.insert(format!("{}", i), m);
                }
                black.insert(format!("{}", i), vec![]);
            }
        }
        if MEDIA {
            for (k, v) in to_populate().into_iter() {
                let m: M = M::new(k.clone(), v);
                if MV {
                    let mut buf = AllocRingBuffer::with_capacity(MV_SIZE);
                    buf.push(m);
                    white2.insert(k.clone(), buf);
                } else {
                    white.insert(k.clone(), m);
                }
                black.insert(k, vec![]);
            }
        }
        // let (sender, mut receiver) = mpsc::channel(1000);
        let (sender, mut receiver) = flume::unbounded();
        tokio::spawn(async move {
            // let mut client: RPCClient = loop {
            //     let next_ip = PEERS[(id + 1) % T];
            //     let res = MeshClient::connect(format!("http://{next_ip}")).await;
            //     match res {
            //         Ok(client) => {
            //             info!("Connected to peer");
            //             break client;
            //         }
            //         Err(_) => {
            //             tokio::time::sleep(std::time::Duration::from_secs(1)).await;
            //         }
            //     }
            // };
            while let Ok(req) = receiver.recv_async().await {
                rpc_client().server_write(req).await.unwrap();
                // client.server_write(req).await.unwrap();
            }
        });
        let addr = format!("http://{}", PEERS[(id + 1) % T]);
        let channel = tonic::transport::Channel::from_shared(addr)
            .unwrap()
            .connect_lazy();
        CLIENT.set(MeshClient::new(channel)).unwrap();
        let (redis_sender, mut redis_receiver) = mpsc::channel(1000);
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
                info!("Connected to redis");
                while let Some(m) = redis_receiver.recv().await {
                    conn.write_frame_and_flush(&m).await.unwrap();
                }
            });
        }
        CCMeshService {
            id,
            white: Mutex::new(white),
            white2: Mutex::new(white2),
            black: Mutex::new(black),
            vc: Mutex::new(VC::default()),
            next: sender,
            redis: redis_sender,
        }
    }

    pub fn print_cache(&self) {
        // let white = self.white.lock().unwrap();
        // let black = self.black.lock().unwrap();
        // let white_l: Vec<u8> = bincode::serialize(&white.clone()).unwrap();
        // let black_l: Vec<u8> = bincode::serialize(&black.clone()).unwrap();
        // info!("white:   {}", white_l.len());
        // info!("black:   {}", black_l.len());
        // info!(
        //     "white:   {:?}",
        //     white
        //         .iter()
        //         .filter(|(_, m)| m.vc != VC::default())
        //         .collect::<Vec<_>>()
        // );
        // info!(
        //     "black:   {:?}",
        //     black
        //         .iter()
        //         .filter(|(_, ms)| ms.len() > 1)
        //         .collect::<Vec<_>>()
        // );
    }

    pub fn get_deps(
        black: &MutexGuard<Black>,
        deps: &HashMap<String, VC>,
        todo: &mut HashSet<(String, VC)>,
    ) {
        for (kk, vc) in deps.iter() {
            if todo.contains(&(kk.clone(), vc.clone())) {
                continue;
            }
            let bkk = black.get(kk).unwrap();
            let find = bkk.iter().find(|&meta| meta.vc == *vc);
            if find.is_none() {
                continue;
            }
            let meta = find.unwrap();
            todo.insert((kk.clone(), vc.clone()));
            Self::get_deps(black, &meta.deps, todo);
        }
    }

    pub fn get_deps2(
        black: &mut MutexGuard<Black>,
        deps: &HashMap<String, VC>,
        todo: &mut HashMap<String, M>,
    ) {
        for (kk, vc) in deps.iter() {
            // let mut lower = VC::default();
            if let Some(vc2) = todo.get(kk) {
                if vc <= &vc2.vc {
                    continue;
                }
                // else {
                //     lower = vc2.vc.clone();
                // }
            }
            let bkk = black.get_mut(kk);
            if bkk.is_none() {
                continue;
            }
            let bkk = bkk.unwrap();

            let mut candidates = vec![];
            let mut idx = 0;
            while idx < bkk.len() {
                let meta = &bkk[idx];
                if meta.vc <= *vc {
                    candidates.push(bkk.remove(idx));
                } else {
                    idx += 1;
                }
            }
            // #[allow(clippy::neg_cmp_op_on_partial_ord)]
            // let mut candidates = bkk
            //     .iter()
            //     .filter(|&meta| meta.vc <= *vc && !(meta.vc <= lower));
            // let m1 = candidates.next();
            // if m1.is_none() {
            //     continue;
            // }
            // let mut merged = m1.unwrap().clone();
            // TODO: remove now?
            if candidates.is_empty() {
                continue;
            }
            let mut merged = candidates.remove(0);
            for m in candidates {
                merged.merge_into(&m);
            }
            todo.insert_or_merge(kk.clone(), merged.no_deps());
            Self::get_deps2(black, &merged.deps, todo);
        }
    }

    pub fn pull_deps2(&self, deps: &HashMap<String, VC>, k: K, m: Option<M>) -> Option<M> {
        let mut black = self.black.lock().unwrap();
        let mut todo = HashMap::default();
        Self::get_deps2(&mut black, deps, &mut todo);
        // let mut res = HashMap::default();
        // for (kk, vc) in todo.iter() {
        //     let bkk = black.get_mut(kk).unwrap();
        //     let mut keep = vec![];
        //     for meta in bkk.iter() {
        //         if meta.vc <= *vc {
        //             res.insert_or_merge(kk.clone(), meta.no_deps());
        //             keep.push(false);
        //         } else {
        //             keep.push(true);
        //         }
        //     }
        //     let mut iter = keep.iter();
        //     bkk.retain(|_| *iter.next().unwrap());
        // }
        drop(black);
        if MV {
            let mut white2 = self.white2.lock().unwrap();
            for (k_, m_) in todo.into_iter() {
                let buf = white2.get_mut(&k_).unwrap();
                let new_m = m_.merge(buf.back().unwrap());
                buf.push(new_m);
            }
            if let Some(m) = m {
                let buf = white2.get_mut(&k).unwrap();
                let new_m = m.merge(buf.back().unwrap());
                buf.push(new_m);
                return None;
            } else {
                let buf = white2.get_mut(&k).unwrap();
                let vc_in_deps = deps.get(&k);
                if let Some(vc_in_deps) = vc_in_deps {
                    for m in buf.iter() {
                        if m.vc == *vc_in_deps {
                            return Some(m.clone());
                        }
                    }
                    return None;
                } else {
                    let keys1: HashSet<&String> = deps.keys().collect();
                    for m in buf.iter() {
                        let keys2: HashSet<&String> = m.deps.keys().collect();
                        let keys3 = keys2.intersection(&keys1);
                        let mut valid = true;
                        for kk in keys3 {
                            let vc = deps.get(*kk).unwrap();
                            if m.vc != *vc {
                                valid = false;
                                break;
                            }
                        }
                        if valid {
                            return Some(m.clone());
                        }
                    }
                    return None;
                }
            }
        } else {
            let mut white = self.white.lock().unwrap();
            white.merge_into_no_deps(&todo);
            if let Some(m) = m {
                white.insert_or_merge(k, m);
                None
            } else {
                if let Some(m) = white.get(&k) {
                    Some(m.clone())
                } else {
                    panic!("pull_deps2: key {} not found", k);
                }
            }
        }
    }

    pub fn pull_deps(&self, deps: &HashMap<String, VC>, k: K, m: Option<M>) -> Option<M> {
        let mut black = self.black.lock().unwrap();
        let mut todo = HashSet::default();
        Self::get_deps(&black, deps, &mut todo);
        let mut versionset: HashMap<String, VC> = HashMap::default();
        for (kk, vc) in todo.iter() {
            versionset.insert_or_merge(kk.clone(), vc.clone());
        }
        let mut res: HashMap<String, M> = HashMap::default();
        for (kk, vc) in versionset.iter() {
            let bkk = black.get_mut(kk).unwrap();
            let mut keep = vec![];
            for meta in bkk.iter() {
                if meta.vc <= *vc {
                    res.insert_or_merge(kk.clone(), meta.no_deps());
                    keep.push(false);
                } else {
                    keep.push(true);
                }
            }
            let mut iter = keep.iter();
            bkk.retain(|_| *iter.next().unwrap());
        }
        drop(black);
        let mut white = self.white.lock().unwrap();
        white.merge_into_no_deps(&res);
        if let Some(m) = m {
            white.insert_or_merge(k, m);
            None
        } else {
            Some(white.get(&k).unwrap().clone())
        }
    }
}

#[tonic::async_trait]
impl Mesh for CCMeshService {
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
        let k = req.key;
        // let deps: HashMap<String, VC> = serde_json::from_slice(&req.deps).unwrap();
        let deps: HashMap<String, VC> = serde_json::from_str(&req.deps).unwrap();
        let res = self.pull_deps2(&deps, k, None);
        // let res = self.white.lock().unwrap().get(&k).unwrap().clone();
        // assert!(res.deps.is_empty());
        self.print_cache();
        if res.is_none() {
            return Ok(Response::new(ClientReadResponse {
                value: "None".to_string(),
                vc: serde_json::to_string(&VC::default()).unwrap(),
            }));
        }
        let res = res.unwrap();
        Ok(Response::new(ClientReadResponse {
            value: res.value,
            vc: serde_json::to_string(&res.vc).unwrap(),
            // vc: serde_json::to_vec(&res.vc).unwrap(),
        }))
    }

    async fn client_write(
        &self,
        request: Request<ClientWriteRequest>,
    ) -> Result<Response<ClientWriteResponse>, Status> {
        // if rand::random::<u64>() % 1000 == 0 {
        //     let black = self.black.lock().unwrap();
        //     let mut total_size = 0;
        //     for (k, ms) in black.iter() {
        //         if ms.len() <= 1 {
        //             continue;
        //         }
        //         for m in ms[1..].iter() {
        //             total_size += 12;
        //             for (kk, vc) in m.deps.iter() {
        //                 total_size += 8;
        //                 total_size += 3;
        //             }
        //         }
        //     }
        //     println!("black: {}", total_size);
        //     // let white = self.white.lock().unwrap();
        //     // let black = self.black.lock().unwrap();
        //     let white2 = self.white2.lock().unwrap();
        //     let mut white_size = 0;
        //     for (k, m) in white2.iter() {
        //         // white22.insert(k.clone(), m.back());
        //         if m.len() == 0 {
        //             continue;
        //         }
        //         white_size += m.back().unwrap().deps.len() * 11;
        //     }
        //     println!("white: {}", white_size);
        //     // let white_l: Vec<u8> = bincode::serialize(&white.clone()).unwrap();
        //     // let white2_l: Vec<u8> = bincode::serialize(&white22).unwrap();
        //     // let black_l: Vec<u8> = bincode::serialize(&black.clone()).unwrap();
        //     // println!("white:   {}", white_l.len());
        //     // println!("white len: {}", white.len());
        //     // println!("white2: {}", white2_l.len());
        //     // println!("black:   {}", black_l.len());
        //     // println!("black len: {}", black.len());
        // }
        let req = request.into_inner();
        let key = req.key;
        let res: VC;
        {
            let mut vc = self.vc.lock().unwrap();
            vc.increment(self.id);
            res = vc.clone();
        }
        // let deps: HashMap<String, VC> = serde_json::from_slice(&req.deps).unwrap();
        let mut deps: HashMap<String, VC> = serde_json::from_str(&req.deps).unwrap();
        let local: HashMap<K, M> = serde_json::from_str(&req.local).unwrap();
        for (k, m) in local.iter() {
            deps.insert_or_merge(k.clone(), m.vc.clone());
            // match self.black.lock().unwrap().entry(k) {
            //     Entry::Occupied(mut e) => {
            //         e.get_mut().push(m);
            //     }
            //     Entry::Vacant(e) => {
            //         e.insert(vec![m]);
            //     }
            // }
        }
        let m: M = M {
            key: key.clone(),
            value: req.value,
            vc: res.clone(),
            deps,
        };
        // let start = std::time::Instant::now();
        let m_cp = m.clone();
        {
            let mut blk = self.black.lock().unwrap();
            for (k, m) in local.into_iter() {
                match blk.entry(k) {
                    Entry::Occupied(mut e) => {
                        if CHEKC_BLK {
                            let mut found = false;
                            for mm in e.get_mut().iter() {
                                if mm.vc == m.vc {
                                    found = true;
                                    break;
                                }
                            }
                            if !found {
                                e.get_mut().push(m);
                            }
                        } else {
                            e.get_mut().push(m);
                        }
                    }
                    Entry::Vacant(e) => {
                        e.insert(vec![m]);
                    }
                }
            }
            match blk.entry(key.clone()) {
                Entry::Occupied(mut e) => {
                    if CHEKC_BLK {
                        let mut found = false;
                        for mm in e.get_mut().iter() {
                            if mm.vc == m.vc {
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            e.get_mut().push(m_cp);
                        }
                    } else {
                        e.get_mut().push(m_cp);
                    }
                }
                Entry::Vacant(e) => {
                    e.insert(vec![m_cp]);
                }
            }
        }
        // println!("black: {}", start.elapsed().as_micros());
        // write to redis
        if DURABLE {
            self.redis.send(m.no_deps()).await.unwrap();
        }
        // let stream = TcpStream::connect(format!("{REDISIP}:28080"))
        //     .await
        //     .unwrap();
        // let mut conn = RedisConn::new(0, stream, REDIS_CODING);
        // conn.write_frame_and_flush(&m.no_deps()).await.unwrap();
        // send to neighbor
        // let start = std::time::Instant::now();
        let next_req = ServerWriteRequest {
            key,
            value: m.value,
            // vc: serde_json::to_vec(&m.vc).unwrap(),
            // deps: serde_json::to_vec(&m.deps).unwrap(),
            vc: serde_json::to_string(&m.vc).unwrap(),
            deps: serde_json::to_string(&m.deps).unwrap(),
            headid: self.id as u32,
        };
        self.next.send(next_req).unwrap();
        // rpc_client().server_write(next_req).await.unwrap();
        // println!("rpc: {}", start.elapsed().as_micros());
        // self.print_cache();
        Ok(Response::new(ClientWriteResponse {
            // vc: serde_json::to_vec(&res).unwrap(),
            vc: serde_json::to_string(&res).unwrap(),
        }))
    }

    async fn server_write(
        &self,
        request: Request<ServerWriteRequest>,
    ) -> Result<Response<()>, Status> {
        let req: ServerWriteRequest = request.into_inner();
        if req.headid != ((self.id + 1) % T) as u32 {
            let vc: VC = serde_json::from_str(&req.vc).unwrap();
            let deps: HashMap<K, VC> = serde_json::from_str(&req.deps).unwrap();
            {
                let m = M {
                    key: req.key.clone(),
                    value: req.value.clone(),
                    vc,
                    deps,
                };
                match self.black.lock().unwrap().entry(req.key.clone()) {
                    Entry::Vacant(e) => {
                        e.insert(vec![m]);
                    }
                    Entry::Occupied(mut e) => {
                        e.get_mut().push(m);
                    }
                }
            }
            // self.get_or_connect().await.server_write(req).await.unwrap();
            self.next.send(req).unwrap();
            // rpc_client().server_write(req).await.unwrap();
            // self.print_cache();
            return Ok(Response::new(()));
        }
        // let req_vc: VC = serde_json::from_slice(&req.vc).unwrap();
        // let req_deps: HashMap<String, VC> = serde_json::from_slice(&req.deps).unwrap();
        let req_vc: VC = serde_json::from_str(&req.vc).unwrap();
        let req_deps: HashMap<String, VC> = serde_json::from_str(&req.deps).unwrap();
        let res_vc: VC;
        {
            let mut vc = self.vc.lock().unwrap();
            vc.merge_into(&req_vc);
            res_vc = vc.clone();
        }
        self.pull_deps2(
            &req_deps,
            req.key.clone(),
            Some(M {
                key: req.key,
                value: req.value,
                vc: res_vc,
                deps: HashMap::default(),
            }),
        );
        self.print_cache();
        Ok(Response::new(()))
    }

    async fn is_visible(
        &self,
        request: Request<IsVisibleRequest>,
    ) -> Result<Response<IsVisibleResponse>, Status> {
        let req = request.into_inner();
        let vc: VC = serde_json::from_str(&req.vc).unwrap();
        let current = self.white.lock().unwrap().get(&req.key).unwrap().vc.clone();
        if current >= vc {
            Ok(Response::new(IsVisibleResponse { res: true }))
        } else {
            let black = self.black.lock().unwrap();
            let bk = black.get(&req.key).unwrap();
            for m in bk {
                if m.vc == vc {
                    drop(black);
                    let mut deps = HashMap::default();
                    deps.insert(req.key.clone(), vc);
                    self.pull_deps2(&deps, req.key.clone(), None);
                    return Ok(Response::new(IsVisibleResponse { res: true }));
                }
            }
            return Ok(Response::new(IsVisibleResponse { res: false }));
        }
    }
}

pub async fn run(id: usize) {
    let ccmesh_service = CCMeshService::new(id);

    Server::builder()
        .add_service(MeshServer::new(ccmesh_service))
        .serve("0.0.0.0:18080".parse().unwrap())
        .await
        .unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn get_deps_test1() {
        let s = serde_json::json!(
            {
                "a": [{
                    "key": "a",
                    "value": "a",
                    "vc": [1, 0, 0],
                    "deps": {
                        "b": [0, 0, 0]
                    }
                }],
                "b": [{
                    "key": "b",
                    "value": "b",
                    "vc": [0, 0, 0],
                    "deps": {}
                }]
            }
        );
        let black: Black = serde_json::from_value(s).unwrap();
        let black = Mutex::new(black);

        let mut todo = HashSet::default();
        let deps: HashMap<String, VC> = {
            let mut deps = HashMap::default();
            deps.insert("a".into(), [1, 0, 0].into());
            deps
        };
        {
            let black = black.lock().unwrap();
            CCMeshService::get_deps(&black, &deps, &mut todo);
        }
        assert_eq!(todo.len(), 2);
        assert!(todo.contains(&("a".to_string(), VC::new([1, 0, 0]))));
        assert!(todo.contains(&("b".to_string(), VC::new([0, 0, 0]))));
        todo.clear();

        let deps: HashMap<String, VC> = {
            let mut deps = HashMap::default();
            deps.insert("b".into(), [0, 0, 0].into());
            deps
        };
        {
            let black = black.lock().unwrap();
            CCMeshService::get_deps(&black, &deps, &mut todo);
        }
        assert_eq!(todo.len(), 1);
        assert!(todo.contains(&("b".to_string(), VC::new([0, 0, 0]))));
    }

    #[test]
    fn get_deps_test2() {
        let s = serde_json::json!(
        {
            "a": [{
                "key": "a",
                "value": "a",
                "vc": [2, 0, 0],
                "deps": {
                    "b": [0, 1, 0]
                }
            }],
            "b": [{
                "key": "b",
                "value": "b",
                "vc": [0, 1, 0],
                "deps": {
                    "c": [0, 0, 0]
                }
            }],
            "c": [{
                "key": "c",
                "value": "c",
                "vc": [0, 0, 0],
                "deps": {}
            }]
        });
        let black: Black = serde_json::from_value(s).unwrap();
        let black = Mutex::new(black);

        let mut todo = HashSet::default();
        let deps: HashMap<String, VC> = {
            let mut deps = HashMap::default();
            deps.insert("a".into(), [2, 0, 0].into());
            deps
        };
        {
            let black = black.lock().unwrap();
            CCMeshService::get_deps(&black, &deps, &mut todo);
        }
        assert_eq!(todo.len(), 3);
        assert!(todo.contains(&("a".to_string(), VC::new([2, 0, 0]))));
        assert!(todo.contains(&("b".to_string(), VC::new([0, 1, 0]))));
        assert!(todo.contains(&("c".to_string(), VC::new([0, 0, 0]))));
        todo.clear();
    }

    #[test]
    fn get_deps_test3() {
        let s = serde_json::json!(
        {
            "a": [{
                "key": "a",
                "value": "a",
                "vc": [2, 2, 0],
                "deps": {
                    "b": [0, 1, 0],
                    "c": [0, 0, 0]
                }
            }],
            "b": [{
                "key": "b",
                "value": "b",
                "vc": [0, 1, 0],
                "deps": {
                    "c": [0, 0, 1]
                }
            }, {
                "key": "b",
                "value": "b",
                "vc": [1, 0, 0],
                "deps": {}
            }],
            "c": [{
                "key": "c",
                "value": "c",
                "vc": [0, 0, 0],
                "deps": {}
            }, {
                "key": "c",
                "value": "c",
                "vc": [0, 0, 1],
                "deps": {}
            }]
        });
        let black: Black = serde_json::from_value(s).unwrap();
        let black = Mutex::new(black);

        let mut todo = HashSet::default();
        let deps: HashMap<String, VC> = {
            let mut deps = HashMap::default();
            deps.insert("a".into(), [2, 2, 0].into());
            deps
        };
        {
            let black = black.lock().unwrap();
            CCMeshService::get_deps(&black, &deps, &mut todo);
        }
        assert_eq!(todo.len(), 4);
        assert!(todo.contains(&("a".to_string(), VC::new([2, 2, 0]))));
        assert!(todo.contains(&("b".to_string(), VC::new([0, 1, 0]))));
        assert!(todo.contains(&("c".to_string(), VC::new([0, 0, 0]))));
        assert!(todo.contains(&("c".to_string(), VC::new([0, 0, 1]))));
        todo.clear();
    }

    #[tokio::test]
    async fn pull_deps_test1() {
        let mut service = CCMeshService::new(0);
        let s = serde_json::json!(
        {
            "a": [{
                "key": "a",
                "value": "a",
                "vc": [2, 2, 0],
                "deps": {
                    "b": [0, 1, 0],
                    "c": [0, 0, 0]
                }
            }],
            "b": [{
                "key": "b",
                "value": "b",
                "vc": [0, 1, 0],
                "deps": {
                    "c": [0, 0, 1]
                }
            }, {
                "key": "b",
                "value": "b",
                "vc": [1, 0, 0],
                "deps": {}
            }],
            "c": [{
                "key": "c",
                "value": "c",
                "vc": [0, 0, 0],
                "deps": {}
            }, {
                "key": "c",
                "value": "c",
                "vc": [0, 0, 1],
                "deps": {}
            }]
        });
        let black: Black = serde_json::from_value(s).unwrap();
        service.black = Mutex::new(black);
        let s = serde_json::json!(
        {
            "a": {
                "key": "a",
                "value": "a",
                "vc": [3, 1, 0],
                "deps": {}
            },
            "b": {
                "key": "b",
                "value": "b",
                "vc": [0, 0, 0],
                "deps": {}
            },
            "c": {
                "key": "c",
                "value": "c",
                "vc": [0, 0, 0],
                "deps": {}
            }
        });
        let white: White = serde_json::from_value(s).unwrap();
        service.white = Mutex::new(white);
        // assert!(todo.contains(&("a".to_string(), VC::new([2, 2, 0]))));
        // assert!(todo.contains(&("b".to_string(), VC::new([0, 1, 0]))));
        // assert!(todo.contains(&("c".to_string(), VC::new([0, 0, 0]))));
        // assert!(todo.contains(&("c".to_string(), VC::new([0, 0, 1]))));
        let deps: HashMap<String, VC> = {
            let mut deps = HashMap::default();
            deps.insert("a".into(), [2, 2, 0].into());
            deps
        };
        service.pull_deps(&deps, "a".into(), None);
        let black = service.black.lock().unwrap();
        assert_eq!(black.len(), 3);
        assert_eq!(black.get("a").unwrap().len(), 0);
        assert_eq!(black.get("b").unwrap().len(), 1);
        assert_eq!(black.get("c").unwrap().len(), 0);
        assert_eq!(
            black.get("b").unwrap().first().unwrap().vc,
            [1, 0, 0].into()
        );
        drop(black);
        let white = service.white.lock().unwrap();
        assert_eq!(white.len(), 3);
        assert_eq!(white.get("a").unwrap().vc, [3, 2, 0].into());
        assert_eq!(white.get("b").unwrap().vc, [0, 1, 0].into());
        assert_eq!(white.get("c").unwrap().vc, [0, 0, 1].into());
    }
}
