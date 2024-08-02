use crate::faas::mesh_client::MeshClient;
use crate::service::{rpc_client, CLIENTS};
use hz_config::*;
use hz_workload::Workload;
use rustc_hash::FxHashMap as HashMap;
use rustc_hash::FxHashSet as HashSet;
use serde::{Deserialize, Serialize};

pub fn setup_clients() {
    for idx in 0..T {
        let addr = format!("http://{}", PEERS[idx]);
        let channel = tonic::transport::Channel::from_shared(addr)
            .unwrap()
            .connect_lazy();
        CLIENTS[idx].set(MeshClient::new(channel)).unwrap();
    }
}

#[derive(Default, Debug, Clone, Serialize, Deserialize)]
pub struct GoClient {
    // pub id: String,
    pub istail: bool,
    pub workload: Workload,
    // pub deps: HashMap<K, VC>,
    pub reads: HashSet<K>,
    pub writes: HashMap<K, V>,
    pub input: String,
    pub low: i32,
    pub high: i32,
    pub abort: bool,
}

impl GoClient {
    pub fn new() -> Self {
        Self {
            istail: false,
            abort: false,
            low: 0,
            high: std::i32::MAX,
            ..Default::default()
        }
    }
}

#[cfg(test)]
mod tests {}
