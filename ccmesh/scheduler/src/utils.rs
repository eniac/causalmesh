use bytes::Bytes;
use hz_config::*;
use hz_workload::*;
use lazy_static::lazy_static;

thread_local! {
    static GCLIENT: hyper::Client<hyper::client::HttpConnector, hyper::Body> = hyper::Client::new();
}

lazy_static! {
    static ref WORKLOADS01: Vec<Workload> = {
        let mut res = vec![];
        if SCALE {
            return res;
        }
        let mut builder = WorkloadBuilder::default()
            .num_read(0)
            .num_write(1)
            .num_migrate(0)
            .zipf(1.0)
            // .uniform()
            .delay_writes();
        for _ in 0..1000000 {
            res.push(builder.build());
        }
        res
    };
    static ref WORKLOADS20: Vec<Workload> = {
        let mut res = vec![];
        if SCALE {
            return res;
        }
        let mut builder = WorkloadBuilder::default()
            .num_read(2)
            .num_write(0)
            .num_migrate(0)
            .zipf(1.0)
            // .uniform()
            .delay_writes();
        for _ in 0..1000000 {
            res.push(builder.build());
        }
        res
    };
    static ref WORKLOADS21: Vec<Workload> = {
        let mut res = vec![];
        if !SCALE {
            return res;
        }
        let mut builder = WorkloadBuilder::default()
            .num_read(2)
            .num_write(1)
            .num_migrate(0)
            .uniform();
        for _ in 0..1000000 {
            res.push(builder.build());
        }
        res
    };
}

pub fn get_01() -> Workload {
    WORKLOADS01[rand::random::<usize>() % WORKLOADS01.len()].clone()
}

pub fn get_20() -> Workload {
    WORKLOADS20[rand::random::<usize>() % WORKLOADS20.len()].clone()
}

pub fn get_21() -> Workload {
    WORKLOADS21[rand::random::<usize>() % WORKLOADS21.len()].clone()
}

// pub fn get_builder(nr: i32, nw: i32) -> WorkloadBuilder {
//     WorkloadBuilder::default()
//         .num_read(nr)
//         .num_write(nw)
//         .num_migrate(0)
//         .zipf(1.0)
// }

pub async fn send_req(nightcore_idx: usize, req: String, uri: &str) -> Bytes {
    let nightcore;
    if uri == "Entry" {
        if rand::random() {
            nightcore =
                "http://".to_owned() + &NIGHTCORES[nightcore_idx].to_owned() + "/function/Entry1";
        } else {
            nightcore =
                "http://".to_owned() + &NIGHTCORES[nightcore_idx].to_owned() + "/function/Entry2";
        }
    } else {
        nightcore =
            "http://".to_owned() + &NIGHTCORES[nightcore_idx].to_owned() + "/function/" + uri;
    }
    let r = hyper::Request::builder()
        .method(hyper::Method::POST)
        .uri(nightcore)
        .header("content-type", "application/json")
        // .header("Connection", "close")
        .body(hyper::Body::from(req))
        .unwrap();
    // let client = hyper::Client::new();
    let client = GCLIENT.with(|c| c.clone());
    let resp = client.request(r).await.unwrap();
    hyper::body::to_bytes(resp.into_body()).await.unwrap()
}
