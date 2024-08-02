pub mod con {
    #![allow(clippy::derive_partial_eq_without_eq)]
    tonic::include_proto!("con");
}
pub mod goclient;
pub mod service;
pub mod utils;
