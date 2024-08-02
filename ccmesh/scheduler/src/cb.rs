use crate::utils::*;
use hyper::{Body, Request, Response};
use hz_causal::*;
use hz_config::*;
use hz_cb::goclient::GoClient;
use hz_workload::{Workload, MOVIES};
use rustc_hash::FxHashMap as HashMap;
use std::collections::VecDeque;
use std::convert::Infallible;

pub async fn cb_service_nocache(_req: Request<Body>) -> Result<Response<Body>, Infallible> {
    let mut workloads = VecDeque::with_capacity(NLAMBDA);
    {
        for _ in 0..NLAMBDA - 1 {
            workloads.push_back(get_20());
        }
        workloads.push_back(get_01());
    }
    let mut c = GoClient::new();
    let mut workloads = workloads.clone();
    for i in 0..NLAMBDA {
        c.workload = workloads.pop_front().unwrap();
        let idx = rand::random::<usize>() % T;
        let req = serde_json::to_string(&c).unwrap();
        let res = send_req(idx, req, "Entry").await;
    }
    Ok(Response::new(Body::from("OK")))
}

pub async fn cb_service(_req: Request<Body>) -> Result<Response<Body>, Infallible> {
    let mut workloads = VecDeque::with_capacity(NLAMBDA);
    {
        for _ in 0..NLAMBDA - 1 {
            workloads.push_back(get_20());
        }
        workloads.push_back(get_01());
    }
    let mut c = GoClient::new();
    let mut workloads = workloads.clone();
    for i in 0..NLAMBDA {
        if i == NLAMBDA - 1 {
            c.istail = true;
        }
        c.workload = workloads.pop_front().unwrap();
        let idx = rand::random::<usize>() % T;
        let req = serde_json::to_string(&c).unwrap();
        let res = send_req(idx, req, "Entry").await;
        let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
        c.upstream = idx;
        // if res_c.abort {
        //     continue 'outer;
        // }
        c.deps = res_c.deps;
        c.writes = res_c.writes;
        // c.local = res_c.local;
    }
    Ok(Response::new(Body::from("OK")))
}

pub async fn cb_service0(_req: Request<Body>) -> Result<Response<Body>, Infallible> {
    let mut workloads = VecDeque::with_capacity(NLAMBDA);
    for _ in 0..NLAMBDA {
        workloads.push_back(get_21());
    }
    'outer: loop {
        let mut c = GoClient::new();
        let mut workloads = workloads.clone();
        for _ in 0..NLAMBDA {
            c.workload = workloads.pop_front().unwrap();
            let req = serde_json::to_string(&c).unwrap();
            let idx = rand::random::<usize>() % T;
            let res = send_req(idx, req, "Entry").await;
            let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
            // if res_c.abort {
            //     continue 'outer;
            // }
            c.deps = res_c.deps;
            c.writes = res_c.writes;
            // c.local = res_c.local;
        }
        break;
    }
    Ok(Response::new(Body::from("OK")))
}

pub async fn cb_service2(_req: Request<Body>) -> Result<Response<Body>, Infallible> {
    let workload: Workload = vec![];
    let mut c = GoClient::new();
    c.workload = workload;
    // let req_id = uuid::Uuid::new_v4().to_string();
    // let req_id = req_id.split("-").last().unwrap().to_string();
    let req_id = (rand::random::<usize>() % 100000).to_string();
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
                let user_id = rand::random::<usize>() % 1000;
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
                let movie_id = rand::random::<usize>() % 1000;
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
    c.deps.merge_into(&h1.deps);
    c.writes.extend(h1.writes);
    c.deps.merge_into(&h2.deps);
    c.writes.extend(h2.writes);
    c.deps.merge_into(&h3.deps);
    c.writes.extend(h3.writes);
    c.deps.merge_into(&h4.deps);
    c.writes.extend(h4.writes);
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
        let req = serde_json::to_string(&c).unwrap();
        let res = send_req(idx, req, "composeReview").await;
        let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
        res_c
    };
    c.deps = res_c.deps;
    c.writes = res_c.writes;
    // c.local.clear();
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
        let req = serde_json::to_string(&c).unwrap();
        let res = send_req(idx, req, "reviewStorage").await;
        let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
        res_c
    };
    c.deps = res_c.deps;
    c.writes = res_c.writes;
    // c.local = res_c.local;
    let (h6, h7) = tokio::join!(
        {
            let mut c = c.clone();
            let req_id = req_id.clone();
            let user_id = review["user_id"].clone();
            async move {
                let js = serde_json::json!(
                    {
                        "Function": "UploadUserReview",
                        "user_id": user_id,
                        "review_id": req_id,
                    }
                );
                c.input = serde_json::to_string(&js).unwrap();
                let idx = rand::random::<usize>() % T;
                let req = serde_json::to_string(&c).unwrap();
                let res = send_req(idx, req, "userReview").await;
                let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
                res_c
            }
        },
        {
            let mut c = c.clone();
            let req_id = req_id.clone();
            let movie_id = review["movie_id"].clone();
            async move {
                let js = serde_json::json!(
                    {
                        "Function": "UploadMovieReview",
                        "movie_id": movie_id,
                        "review_id": req_id,
                    }
                );
                c.input = serde_json::to_string(&js).unwrap();
                let idx = rand::random::<usize>() % T;
                let req = serde_json::to_string(&c).unwrap();
                let res = send_req(idx, req, "movieReview").await;
                let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
                res_c
            }
        }
    );
    Ok(Response::new(Body::from("OK")))
}

pub async fn cb_service3(_req: Request<Body>) -> Result<Response<Body>, Infallible> {
    let workload: Workload = vec![];
    let mut c = GoClient::new();
    c.workload = workload;
    let movie_id = MOVIES[rand::random::<usize>() % 1000].to_string();
    let js = serde_json::json!(
        {
            "Function": "ReadMovieReviews",
            "movie_id": movie_id,
        }
    );
    c.input = serde_json::to_string(&js).unwrap();
    let idx = rand::random::<usize>() % T;
    let req = serde_json::to_string(&c).unwrap();
    let res = send_req(idx, req, "movieReview").await;
    let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
    let ids = serde_json::from_str::<Vec<String>>(&res_c.input).unwrap();
    if ids.is_empty() {
        return Ok(Response::new(Body::from("OK")));
    }
    c.deps = res_c.deps;
    c.writes = res_c.writes;
    // c.local = res_c.local;
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
    // let res_c = serde_json::from_slice::<GoClient>(&res).unwrap();
    Ok(Response::new(Body::from("OK")))
}

