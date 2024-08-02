use crate::cb::mesh_client::MeshClient;
use crate::service::{rpc_client, CLIENTS};
use hz_config::*;
use hz_workload::Workload;
use rustc_hash::FxHashMap as HashMap;
use rustc_hash::FxHashSet as HashSet;
use serde::{Deserialize, Serialize};
use std::collections::hash_map::Entry;

pub fn setup_clients() {
    for idx in 0..T {
        let addr = format!("http://{}", PEERS[idx]);
        let channel = tonic::transport::Channel::from_shared(addr)
            .unwrap()
            .connect_lazy();
        CLIENTS[idx].set(MeshClient::new(channel)).unwrap();
    }
}

#[derive(Default, Clone, Debug, Serialize, Deserialize)]
pub struct GoClient {
    pub id: String,
    pub upstream: usize,
    pub istail: bool,
    pub workload: Workload,
    pub deps: HashMap<K, VC>,
    pub writes: HashMap<K, V>,
    pub input: String,
}

impl GoClient {
    pub fn new() -> Self {
        let id = uuid::Uuid::new_v4().to_string();
        Self {
            id,
            istail: false,
            ..Default::default()
        }
    }
}