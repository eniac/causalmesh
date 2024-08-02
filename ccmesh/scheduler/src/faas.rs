use crate::utils::*;
use hyper::{Body, Request, Response};
use hz_causal::*;
use hz_config::*;
use hz_faas::goclient::GoClient;
use hz_workload::*;
use rustc_hash::FxHashMap as HashMap;
use rustc_hash::FxHashSet as HashSet;
use std::collections::VecDeque;
use std::convert::Infallible;

pub async fn faas_service(_req: Request<Body>) -> Result<Response<Body>, Infallible> {
    let mut workloads = VecDeque::with_capacity(NLAMBDA);
    {
        for _ in 0..NLAMBDA - 1 {
            workloads.push_back(get_20());
        }
        workloads.push_back(get_01());
    }
    let mut read_set: HashSet<String> = HashSet::default();
    let mut aborts = 0;
    let mut c;
    let mut upstream_id = 0;
    'outer: loop {
        c = GoClient::new();
        for idx in 0..NLAMBDA {
            if idx == NLAMBDA - 1 {
                c.istail = true;
            }
            c.workload = workloads[idx].clone();
            read_set.clear();
            for op in c.workload.iter() {
                if let Op::R(k) = op {
                    read_set.insert(k.clone());
                }
            }
            let idx = rand::random::<usize>() % T;
            let req = serde_json::to_string(&c).unwrap();
            let res = send_req(idx, req, "Entry").await;
            let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
            c.writes = res_c.writes;
            c.abort = res_c.abort;
            c.reads = res_c.reads;
            c.low = std::cmp::max(c.low, res_c.low);
            c.high = std::cmp::min(c.high, res_c.high);
            if c.abort || c.low > c.high {
                aborts += 1;
                continue 'outer;
            }
        }
        // if aborts > 0 {
        //     println!("aborts: {}", aborts);
        // }
        break;
    }
    Ok(Response::new(Body::from("OK")))
}

pub async fn faas_service0(_req: Request<Body>) -> Result<Response<Body>, Infallible> {
    let mut workloads = VecDeque::with_capacity(NLAMBDA);
    for _ in 0..NLAMBDA {
        workloads.push_back(get_21());
    }
    'outer: loop {
        let mut c = GoClient::new();
        let workloads = workloads.clone();
        for idx in 0..NLAMBDA {
            if idx == NLAMBDA - 1 {
                c.istail = true;
            }
            c.workload = workloads[idx].clone();
            let req = serde_json::to_string(&c).unwrap();
            let idx = rand::random::<usize>() % T;
            let res = send_req(idx, req, "Entry").await;
            let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
            c.abort = res_c.abort;
            c.reads = res_c.reads;
            c.writes = res_c.writes;
            c.low = std::cmp::max(c.low, res_c.low);
            c.high = std::cmp::min(c.high, res_c.high);
            if c.abort || c.low > c.high {
                continue 'outer;
            }
        }
        break;
    }
    Ok(Response::new(Body::from("OK")))
}

pub async fn faas_service2(_req: Request<Body>) -> Result<Response<Body>, Infallible> {
    // let req_id = uuid::Uuid::new_v4().to_string();
    let req_id = (rand::random::<usize>() % 100000).to_string();
    let user_id = rand::random::<usize>() % 1000;
    let movie_id = rand::random::<usize>() % 1000;
    let mut upstream_id;
    'outer: loop {
        let workload: Workload = vec![];
        let mut c = GoClient::new();
        c.workload = workload;
        // let ok = c.prepare(idx, upstream_id, &read_set).await;
        let (h1, h2, h3, h4) = tokio::join!(
            {
                let mut c = c.clone();
                let req_id = req_id.clone();
                async move {
                    let js = serde_json::json!(
                        {
                            "Function": "UploadText",
                            "req_id": req_id,
                            "text": "review text",
                        }
                    );
                    c.input = serde_json::to_string(&js).unwrap();
                    let idx = rand::random::<usize>() % T;
                    let req = serde_json::to_string(&c).unwrap();
                    let res = send_req(idx, req, "composeReview").await;
                    let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
                    res_c
                }
            },
            {
                let mut c = c.clone();
                let req_id = req_id.clone();
                async move {
                    let js = serde_json::json!(
                        {
                            "Function": "UploadRating",
                            "req_id": req_id,
                            "rating": "5",
                        }
                    );
                    c.input = serde_json::to_string(&js).unwrap();
                    let idx = rand::random::<usize>() % T;
                    let req = serde_json::to_string(&c).unwrap();
                    let res = send_req(idx, req, "composeReview").await;
                    let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
                    res_c
                }
            },
            {
                let mut c = c.clone();
                let req_id = req_id.clone();
                async move {
                    let js = serde_json::json!(
                        {
                            "Function": "UploadUserId",
                            "req_id": req_id,
                            "user_id": user_id.to_string(),
                        }
                    );
                    c.input = serde_json::to_string(&js).unwrap();
                    let idx = rand::random::<usize>() % T;
                    let req = serde_json::to_string(&c).unwrap();
                    let res = send_req(idx, req, "composeReview").await;
                    let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
                    res_c
                }
            },
            {
                let mut c = c.clone();
                let req_id = req_id.clone();
                async move {
                    let js = serde_json::json!(
                        {
                            "Function": "UploadMovieId",
                            "req_id": req_id,
                            "movie_id": MOVIES[movie_id].to_string(),
                        }
                    );
                    c.input = serde_json::to_string(&js).unwrap();
                    let idx = rand::random::<usize>() % T;
                    let req = serde_json::to_string(&c).unwrap();
                    let res = send_req(idx, req, "composeReview").await;
                    let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
                    res_c
                }
            }
        );
        c.writes.extend(h1.writes);
        c.reads.extend(h1.reads);
        c.low = std::cmp::max(c.low, h1.low);
        c.high = std::cmp::min(c.high, h1.high);
        c.writes.extend(h2.writes);
        c.reads.extend(h2.reads);
        c.low = std::cmp::max(c.low, h2.low);
        c.high = std::cmp::min(c.high, h2.high);
        c.writes.extend(h3.writes);
        c.reads.extend(h3.reads);
        c.low = std::cmp::max(c.low, h3.low);
        c.high = std::cmp::min(c.high, h3.high);
        c.writes.extend(h4.writes);
        c.reads.extend(h4.reads);
        c.low = std::cmp::max(c.low, h4.low);
        c.high = std::cmp::min(c.high, h4.high);
        if h1.abort || h2.abort || h3.abort || h4.abort || c.low > c.high {
            continue 'outer;
        }

        let mut read_set: HashSet<String> = HashSet::default();
        read_set.insert(format!("userReview.{}", user_id));
        read_set.insert(format!("movieReview.{}", MOVIES[movie_id]));
        let mut review: HashMap<String, String>;
        let res_c = {
            let mut c = c.clone();
            let req_id = req_id.clone();
            let js = serde_json::json!(
                {
                    "Function": "ComposeAndUpload",
                    "req_id": req_id,
                }
            );
            c.input = serde_json::to_string(&js).unwrap();
            let idx = rand::random::<usize>() % T;
            upstream_id = idx;
            let req = serde_json::to_string(&c).unwrap();
            let res = send_req(idx, req, "composeReview").await;
            let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
            res_c
        };
        c.writes = res_c.writes;
        c.reads = res_c.reads;
        c.low = std::cmp::max(c.low, res_c.low);
        c.high = std::cmp::min(c.high, res_c.high);
        if res_c.abort || c.low > c.high {
            continue 'outer;
        }
        // c.deps.merge_into(&res_c.deps);
        // c.writes.extend(res_c.writes);
        review = serde_json::from_str(&res_c.input).unwrap();
        // review.insert("req_id".to_owned(), req_id.clone());
        review.insert("review_id".to_owned(), req_id.clone());
        let res_c = {
            let js = serde_json::json!(
                {
                    "Function": "StoreReview",
                    "review": serde_json::to_string(&review).unwrap(),
                }
            );
            c.input = serde_json::to_string(&js).unwrap();
            let idx = rand::random::<usize>() % T;
            // let ok = c.prepare(idx, upstream_id, &read_set).await;
            // if !ok {
            //     GoClient::cleanup(c.id.clone()).await;
            //     continue 'outer;
            // }
            upstream_id = idx;
            let req = serde_json::to_string(&c).unwrap();
            let res = send_req(idx, req, "reviewStorage").await;
            let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
            res_c
        };
        c.writes.extend(res_c.writes);
        c.reads.extend(res_c.reads);
        c.low = std::cmp::max(c.low, res_c.low);
        c.high = std::cmp::min(c.high, res_c.high);
        if res_c.abort || c.low > c.high {
            continue 'outer;
        }
        let (h6, h7) = tokio::join!(
            {
                let mut c = c.clone();
                let req_id = req_id.clone();
                let user_id = review["user_id"].clone();
                let read_set = read_set.clone();
                async move {
                    let js = serde_json::json!(
                        {
                            "Function": "UploadUserReview",
                            "user_id": user_id,
                            "review_id": req_id,
                        }
                    );
                    c.istail = true;
                    c.input = serde_json::to_string(&js).unwrap();
                    let idx = rand::random::<usize>() % T;
                    let req = serde_json::to_string(&c).unwrap();
                    let res = send_req(idx, req, "userReview").await;
                    let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
                    Some(res_c)
                }
            },
            {
                let mut c = c.clone();
                let req_id = req_id.clone();
                let movie_id = review["movie_id"].clone();
                let read_set = read_set.clone();
                async move {
                    let js = serde_json::json!(
                        {
                            "Function": "UploadMovieReview",
                            "movie_id": movie_id,
                            "review_id": req_id,
                        }
                    );
                    c.writes.clear();
                    c.istail = true;
                    c.input = serde_json::to_string(&js).unwrap();
                    let idx = rand::random::<usize>() % T;
                    let req = serde_json::to_string(&c).unwrap();
                    let res = send_req(idx, req, "movieReview").await;
                    let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
                    Some(res_c)
                }
            }
        );
        if h6.is_none() || h7.is_none() || h6.as_ref().unwrap().abort {
            continue 'outer;
        }
        c.low = std::cmp::max(c.low, h6.as_ref().unwrap().low);
        c.high = std::cmp::min(c.high, h6.as_ref().unwrap().high);
        c.low = std::cmp::max(c.low, h7.as_ref().unwrap().low);
        c.high = std::cmp::min(c.high, h7.as_ref().unwrap().high);
        if h6.as_ref().unwrap().abort || h7.as_ref().unwrap().abort || c.low > c.high {
            continue 'outer;
        }
        break;
    }
    Ok(Response::new(Body::from("OK")))
}

pub async fn faas_service3(_req: Request<Body>) -> Result<Response<Body>, Infallible> {
    let movie_id = MOVIES[rand::random::<usize>() % 1000].to_string();
    let mut aborts = 0;
    let mut upstream_id = 0;
    'outer: loop {
        let workload: Workload = vec![];
        let mut c = GoClient::new();
        c.workload = workload;
        let js = serde_json::json!(
            {
                "Function": "ReadMovieReviews",
                "movie_id": movie_id,
            }
        );
        c.input = serde_json::to_string(&js).unwrap();
        let idx = rand::random::<usize>() % T;
        let mut read_set = HashSet::default();
        read_set.insert(format!("movieReview.{}", movie_id));
        let req = serde_json::to_string(&c).unwrap();
        let res = send_req(idx, req, "movieReview").await;
        let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
        upstream_id = idx;
        c.writes = res_c.writes;
        c.reads = res_c.reads;
        c.low = res_c.low;
        c.high = res_c.high;
        if res_c.abort || c.low > c.high {
            aborts += 1;
            continue 'outer;
        }
        let ids = serde_json::from_str::<Vec<String>>(&res_c.input).unwrap();
        let mut read_set = HashSet::default();
        for id in ids.iter() {
            read_set.insert(format!("reviewStorage.{}", id));
        }
        let js = serde_json::json!(
            {
                "Function": "ReadReviews",
                "ids": serde_json::to_string(&ids).unwrap(),
            }
        );
        c.input = serde_json::to_string(&js).unwrap();
        let idx = rand::random::<usize>() % T;
        let req = serde_json::to_string(&c).unwrap();
        let res = send_req(idx, req, "reviewStorage").await;
        let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
        if res_c.abort || res_c.low > res_c.high {
            aborts += 1;
            continue 'outer;
        }
        break;
    }
    // if aborts > 0 {
    //     println!("aborts: {}", aborts);
    // }
    Ok(Response::new(Body::from("OK")))
}
