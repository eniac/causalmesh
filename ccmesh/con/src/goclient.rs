use crate::con::mesh_client::MeshClient;
use crate::con::CleanUpRequest;
use crate::con::Prepare1Request;
use crate::con::Prepare2Request;
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
// thread_local! {
//     static CLIENTS: RefCell<HashMap<usize, MeshClient<tonic::transport::Channel>>> = RefCell::new(HashMap::default());
// }

// pub async fn get_client() {
//     CLIENT.with(|client| {
//         tokio::runtime::Handle::current().block_on(async {
//             client.get_or_init(create_client).await;
//         });
//     });
// }

// pub fn on_start() {
//     tokio::runtime::Handle::current().block_on(async {
//         for (idx, peer) in PEERS.iter().enumerate() {
//             let client = MeshClient::connect(*peer).await.unwrap();
//             CLIENTS.with(|clients| {
//                 clients.borrow_mut().insert(idx, client);
//             });
//         }
//     });
// }

// pub async fn tt() {
//     let mut client = CLIENTS.with(|clients| clients.borrow().get(&0).unwrap().clone());
//     client
//         .prepare1(Prepare1Request {
//             id: "id".to_string(),
//             ri: vec!["key".to_string()],
//             rdag: vec![],
//         })
//         .await
//         .unwrap();
// }

#[derive(Default, Clone, Debug, Serialize, Deserialize)]
pub struct GoClient {
    pub id: String,
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

    async fn prepare1(client_id: String, server_id: usize, read_set: HashSet<K>) -> HashMap<K, M> {
        let mut client = rpc_client(server_id);
        // let server_ip = PEERS[server_id];
        // let mut client = MeshClient::connect(format!("http://{server_ip}"))
        //     .await
        //     .unwrap();
        let rs = Vec::<K>::from_iter(read_set);
        let res = client.prepare1(Prepare1Request {
            id: client_id,
            ri: rs.clone(),
            rdag: rs,
        });
        serde_json::from_str(&res.await.unwrap().into_inner().metaset).unwrap()
    }

    fn get_rremotes(mss: &[HashMap<K, M>]) -> Vec<HashMap<String, Vec<usize>>> {
        let mut rremotes = vec![];
        for (i, ms_i) in mss.iter().enumerate() {
            let mut rremote = HashMap::<K, Vec<usize>>::default();
            for (j, ms_j) in mss.iter().enumerate() {
                if i == j {
                    continue;
                }
                for (k, m) in ms_i.iter() {
                    assert!(ms_j.contains_key(k));
                    if !(m.vc >= ms_j.get(k).unwrap().vc) {
                        match rremote.entry(k.clone()) {
                            Entry::Vacant(e) => {
                                e.insert(vec![j]);
                            }
                            Entry::Occupied(mut e) => {
                                e.get_mut().push(j);
                            }
                        }
                    }
                }
            }
            rremotes.push(rremote);
        }
        rremotes
    }

    pub async fn prepare2(client_id: String, server_id: usize, rremote: HashMap<K, Vec<usize>>) {
        let mut client = rpc_client(server_id);
        // let server_ip = PEERS[server_id];
        // let mut client = MeshClient::connect(format!("http://{server_ip}"))
        //     .await
        //     .unwrap();
        client
            .prepare2(Prepare2Request {
                id: client_id,
                rremote: serde_json::to_string(&rremote).unwrap(),
            })
            .await
            .unwrap();
    }

    pub async fn prepare(client_id: String, read_set: HashSet<String>) {
        let mut mss: Vec<HashMap<K, M>> = Vec::new();
        let mut handles = vec![];
        for i in 0..T {
            let handle = tokio::spawn({
                let id = client_id.clone();
                let read_set = read_set.clone();
                async move { GoClient::prepare1(id, i, read_set).await }
            });
            handles.push(handle);
        }
        for handle in handles {
            let ms = handle.await.unwrap();
            mss.push(ms);
        }
        let rremotes = GoClient::get_rremotes(&mss);
        let handles: Vec<_> = rremotes
            .into_iter()
            .enumerate()
            .map(|(i, rremote)| {
                let id = client_id.clone();
                tokio::spawn(async move {
                    Self::prepare2(id, i, rremote).await;
                })
            })
            .collect();
        for handle in handles {
            handle.await.unwrap();
        }
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
mod tests {
    use super::*;

    #[test]
    fn get_rremote_test1() {
        let js = serde_json::json!([
            {
                "1": {
                    "key": "1",
                    "value": "1",
                    "vc": [0, 0, 0],
                    "deps": {}
                },
                "2": {
                    "key": "2",
                    "value": "2",
                    "vc": [1, 0, 0],
                    "deps": {}
                },
            },
            {
                "1": {
                    "key": "1",
                    "value": "1",
                    "vc": [0, 1, 0],
                    "deps": {}
                },
                "2": {
                    "key": "2",
                    "value": "2",
                    "vc": [0, 0, 0],
                    "deps": {}
                },
            },
            {
                "1": {
                    "key": "1",
                    "value": "1",
                    "vc": [0, 0, 0],
                    "deps": {}
                },
                "2": {
                    "key": "2",
                    "value": "2",
                    "vc": [0, 0, 0],
                    "deps": {}
                },
            }
        ]);
        let mss: Vec<HashMap<String, M>> = serde_json::from_value(js).unwrap();
        let rremotes = GoClient::get_rremotes(&mss);
        let res: Vec<HashMap<String, Vec<usize>>> = serde_json::from_value(serde_json::json!([
            {
                "1": [1],
            },
            {
                "2": [0]
            },
            {
                "1": [1],
                "2": [0],
            }
        ]))
        .unwrap();
        assert_eq!(rremotes, res);
    }

    #[test]
    fn get_rremote_test2() {
        let js = serde_json::json!([
            {
                "1": {
                    "key": "1",
                    "value": "1",
                    "vc": [1, 0, 0],
                    "deps": {}
                },
            },
            {
                "1": {
                    "key": "1",
                    "value": "1",
                    "vc": [0, 1, 0],
                    "deps": {}
                },
            },
            {
                "1": {
                    "key": "1",
                    "value": "1",
                    "vc": [0, 0, 0],
                    "deps": {}
                },
            }
        ]);
        let mss: Vec<HashMap<String, M>> = serde_json::from_value(js).unwrap();
        let rremotes = GoClient::get_rremotes(&mss);
        let res: Vec<HashMap<String, Vec<usize>>> = serde_json::from_value(serde_json::json!([
            {
                "1": [1],
            },
            {
                "1": [0],
            },
            {
                "1": [0, 1],
            }
        ]))
        .unwrap();
        assert_eq!(rremotes, res);
    }
}
