pub mod faas {
    #![allow(clippy::derive_partial_eq_without_eq)]
    tonic::include_proto!("faas");
}
pub mod goclient;
pub mod service;
pub mod utils;
