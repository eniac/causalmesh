pub mod opt {
    #![allow(clippy::derive_partial_eq_without_eq)]
    tonic::include_proto!("opt");
}
pub mod goclient;
pub mod service;
pub mod utils;
