use crate::config::T;
use hz_causal::*;
use hz_ipc::connection::Connection;
use tokio::net::TcpStream;

pub type K = String;
pub type V = String;
pub type VC = DenseVC<T>;
pub type M = Meta<K, V, VC>;
pub type RedisConn = Connection<M, TcpStream, 512>;

pub static DURABLE: bool = true;
pub static MEDIA: bool = false;
pub static SCALE: bool = false;
pub static MV: bool = false;
pub static MV_SIZE: usize = 1;
