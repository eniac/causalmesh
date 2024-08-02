use hz_config::*;
use hz_workload::Workload;
use rustc_hash::FxHashMap as HashMap;
use serde::{Deserialize, Serialize};

#[derive(Default, Debug, Clone, Serialize, Deserialize)]
pub struct GoClient {
    pub workload: Workload,
    pub local: HashMap<K, M>,
    pub deps: HashMap<K, VC>,
    pub input: String,
    pub abort: bool,
}

impl GoClient {
    pub fn new() -> Self {
        Self::default()
    }
}
