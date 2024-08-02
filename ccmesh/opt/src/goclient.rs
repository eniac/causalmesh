use crate::opt::mesh_client::MeshClient;
use crate::opt::{CleanUpRequest, PrepareRequest};
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
    pub id: String,
    pub istail: bool,
    pub workload: Workload,
    pub deps: HashMap<K, VC>,
    pub writes: HashMap<K, V>,
    #[serde(skip_serializing, skip_deserializing)]
    pub su: HashMap<K, VC>,
    #[serde(skip_serializing, skip_deserializing)]
    pub ru: HashMap<K, VC>,
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

    pub async fn prepare(
        &mut self,
        server_id: usize,
        upstream_id: usize,
        read_set: &HashSet<K>,
    ) -> bool {
        let mut client = rpc_client(server_id);
        // let server_ip = PEERS[server_id];
        // let mut client = MeshClient::connect(format!("http://{server_ip}"))
        //     .await
        //     .unwrap();
        let resp = client
            .prepare(PrepareRequest {
                id: self.id.clone(),
                upstream: upstream_id as i32,
                keys: read_set.iter().cloned().collect(),
                su: serde_json::to_string(&self.su).unwrap(),
                ru: serde_json::to_string(&self.ru).unwrap(),
            })
            .await
            .unwrap()
            .into_inner();
        if resp.abort {
            return false;
        }
        self.su = serde_json::from_str(&resp.su).unwrap();
        self.ru = serde_json::from_str(&resp.su).unwrap();
        true
    }

    pub async fn cleanup_server(client_id: String, server_id: usize) {
        let mut client = rpc_client(server_id);
        // let server_ip = PEERS[server_id];
        // let mut client = MeshClient::connect(format!("http://{server_ip}"))
        //     .await
        //     .unwrap();
        client
            .clean_up(CleanUpRequest { id: client_id })
            .await
            .unwrap();
    }

    pub async fn cleanup(client_id: String) {
        let handles = (0..T).map(|i| {
            let id = client_id.clone();
            tokio::spawn(async move { GoClient::cleanup_server(id, i).await })
        });
        for handle in handles {
            handle.await.unwrap();
        }
    }
}

#[cfg(test)]
mod tests {}
