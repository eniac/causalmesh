use serde::{Deserialize, Serialize};

#[allow(non_snake_case)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Config {
    pub NLAMBDA: usize,
    pub MAXKEY: i32,
    pub PEERS: Vec<String>,
    pub REDISIP: String,
}

pub const MODE: &str = {
    if cfg!(feature = "ccmesh") {
        "mesh"
    } else if cfg!(feature = "opt") {
        "opt"
    } else if cfg!(feature = "con") {
        "con"
    } else if cfg!(feature = "base") {
        "baseline"
    } else if cfg!(feature = "cb") {
        "cb"
    } else if cfg!(feature = "faas") {
        "faas"
    } else {
        "unknown"
    }
};

fn main() {
    println!("cargo:rerun-if-changed=local.json");
    println!("cargo:rerun-if-changed=cloud.json");
    let json: serde_json::Value = {
        if cfg!(feature = "local") {
            serde_json::from_str(include_str!("local.json")).unwrap()
        } else if cfg!(feature = "cloud") {
            serde_json::from_str(include_str!("cloud.json")).unwrap()
        } else {
            panic!("unknown config")
        }
    };
    let config: Config = serde_json::from_value(json).unwrap();
    let path = std::path::Path::new(&std::env::var("OUT_DIR").unwrap()).join("config.rs");
    let n_peers = config.PEERS.len();
    let peers = config
        .PEERS
        .iter()
        .map(|peer| format!("{}:{}", peer, 18080))
        .collect::<Vec<String>>();
    let nightcores = config
        .PEERS
        .iter()
        .map(|peer| format!("{}:{}", peer, 8080))
        .collect::<Vec<String>>();
    let out: String = format!(
        "pub const MODE: &str = {:?};
pub const T: usize = {};
pub const NLAMBDA: usize = {};
pub const PEERS: [&str; {}] = {:?};
pub const NIGHTCORES: [&str; {}] = {:?};
pub const MAXKEY: i32 = {};
pub const REDISIP: &str = {:?};",
        MODE,
        n_peers,
        config.NLAMBDA,
        n_peers,
        peers,
        n_peers,
        nightcores,
        config.MAXKEY,
        config.REDISIP
    );
    std::fs::write(&path, out).unwrap();
}
