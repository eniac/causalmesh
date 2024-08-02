use hz_config::*;
use hz_mesh::service::cc_mesh::mesh_client::MeshClient;
use hz_mesh::service::cc_mesh::{ClientReadRequest, ClientWriteRequest, IsVisibleRequest};
use rustc_hash::FxHashMap as HashMap;
use std::io::Write;

#[tokio::main(flavor = "current_thread")]
async fn writer() {
    let _ = std::fs::remove_file("writer.txt");
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .append(true)
        .open("writer.txt")
        .unwrap();
    let addr = format!("http://{}", PEERS[0]);
    let mut s0 = MeshClient::connect(addr).await.unwrap();
    let deps: HashMap<K, VC> = HashMap::default();
    let local: HashMap<K, M> = HashMap::default();
    let deps_str = serde_json::to_string(&deps).unwrap();
    let local_str = serde_json::to_string(&local).unwrap();
    loop {
        let res = s0
            .client_write(ClientWriteRequest {
                key: "100".into(),
                value: "value".to_string(),
                deps: deps_str.clone(),
                local: local_str.clone(),
            })
            .await
            .unwrap();
        let res = format!(
            "{} {}\n",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_micros(),
            res.into_inner().vc
        );
        file.write_all(res.as_bytes()).unwrap();
    }
}

async fn reader() {
    let _ = std::fs::remove_file("reader.txt");
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .append(true)
        .open("reader.txt")
        .unwrap();
    let addr = format!("http://{}", PEERS[T - 1]);
    let mut sn = MeshClient::connect(addr).await.unwrap();
    let deps: HashMap<K, VC> = HashMap::default();
    let deps_str = serde_json::to_string(&deps).unwrap();
    loop {
        let res = sn
            .client_read(ClientReadRequest {
                key: "100".into(),
                deps: deps_str.clone(),
            })
            .await
            .unwrap();
        let res = format!(
            "{} {}\n",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_micros(),
            res.into_inner().vc
        );
        file.write_all(res.as_bytes()).unwrap();
    }
}

async fn vis() {
    let mut s0 = MeshClient::connect(format!("http://{}", PEERS[0]))
        .await
        .unwrap();
    let mut sn = MeshClient::connect(format!("http://{}", PEERS[T - 1]))
        .await
        .unwrap();
    let deps: HashMap<K, VC> = HashMap::default();
    let local: HashMap<K, M> = HashMap::default();
    let deps_str = serde_json::to_string(&deps).unwrap();
    let local_str = serde_json::to_string(&local).unwrap();
    loop {
        let start1 = std::time::Instant::now();
        let res = s0
            .client_write(ClientWriteRequest {
                key: "100".into(),
                value: "value".to_string(),
                deps: deps_str.clone(),
                local: local_str.clone(),
            })
            .await
            .unwrap();
        let start2 = std::time::Instant::now();
        let vc = res.into_inner().vc;
        loop {
            let res = sn
                .client_read(ClientReadRequest {
                    key: "100".into(),
                    deps: deps_str.clone(),
                })
                .await
                .unwrap();
            if vc == res.into_inner().vc {
                let dura1 = start1.elapsed().as_micros();
                let dura2 = start2.elapsed().as_micros();
                println!("{}", (dura1 + dura2) / 2);
                break;
            }
        }
    }
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    vis().await;
    // std::thread::spawn(move || {
    //     writer();
    // });
    // reader().await;
    // let mut s0 = MeshClient::connect(PEERS[0]).await.unwrap();
    // let mut sn = MeshClient::connect(PEERS[PEERS.len() - 1]).await.unwrap();
    // let start = std::time::Instant::now();
    // let vc = res.into_inner().vc;
    // loop {
    //     let resp = sn
    //         .is_visible(IsVisibleRequest {
    //             key: "vis".into(),
    //             vc: vc.clone(),
    //         })
    //         .await
    //         .unwrap();
    //     if resp.into_inner().res {
    //         break;
    //     }
    // }
    // println!("Elapsed: {:?}", start.elapsed());
}
