use hyper::service::{make_service_fn, service_fn};
use hyper::{Body, Request, Response, Server};
use hz_config::*;
use scheduler::con::{con_service, con_service0, con_service2};
use scheduler::faas::{faas_service, faas_service0, faas_service2, faas_service3};
use scheduler::mesh::{mesh_service, mesh_service0, mesh_service2, mesh_service3};
use scheduler::cb::{cb_service, cb_service0, cb_service2, cb_service3};
use scheduler::opt::{opt_service, opt_service0, opt_service2, opt_service3};
use std::convert::Infallible;
use tracing::info;

async fn service0(_req: Request<Body>) -> Result<Response<Body>, Infallible> {
    match MODE {
        "mesh" => mesh_service0(_req).await,
        "faas" => faas_service0(_req).await,
        "opt" => opt_service0(_req).await,
        "con" => con_service0(_req).await,
        _ => panic!("unknown mode"),
    }
}

async fn service(_req: Request<Body>) -> Result<Response<Body>, Infallible> {
    match MODE {
        "mesh" => mesh_service(_req).await,
        "con" => con_service(_req).await,
        "opt" => opt_service(_req).await,
        "cb" => cb_service(_req).await,
        "faas" => faas_service(_req).await,
        _ => panic!("unknown mode"),
    }
}

async fn service2(_req: Request<Body>) -> Result<Response<Body>, Infallible> {
    match MODE {
        "mesh" => {
            // mesh_service2(_req).await
            if rand::random() {
                mesh_service2(_req).await
            } else {
                mesh_service3(_req).await
            }
        }
        "con" => con_service2(_req).await,
        "opt" => {
            // opt_service2(_req).await
            if rand::random() {
                opt_service2(_req).await
            } else {
                opt_service3(_req).await
            }
        }
        "cb" => {
            // mesh_service2(_req).await
            if rand::random() {
                cb_service2(_req).await
            } else {
                cb_service3(_req).await
            }
        }
        "faas" => {
            if rand::random() {
                faas_service2(_req).await
            } else {
                faas_service3(_req).await
            }
        }
        _ => panic!("unknown mode"),
    }
}

#[tokio::main(worker_threads = 6)]
async fn main() {
    tracing_subscriber::fmt::init();
    info!("Current Mode: {:?}", MODE);
    match MODE {
        "con" => hz_con::goclient::setup_clients(),
        "opt" => hz_opt::goclient::setup_clients(),
        "mesh" => {}
        "cb" => hz_cb::goclient::setup_clients(),
        "faas" => hz_faas::goclient::setup_clients(),
        _ => panic!("unknown mode"),
    }
    let addr = std::net::SocketAddr::from(([127, 0, 0, 1], 3000));
    // let addr = std::net::SocketAddr::from(([10, 10, 1, 15], 3000));
    let make_svc = make_service_fn(|_conn| async { Ok::<_, Infallible>(service_fn(service)) });
    let server = Server::bind(&addr).serve(make_svc);
    server.await.unwrap();
}
