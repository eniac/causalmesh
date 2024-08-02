pub mod cb {
    #![allow(clippy::derive_partial_eq_without_eq)]
    tonic::include_proto!("cb");
}
pub mod goclient;
pub mod service;
pub mod utils;
