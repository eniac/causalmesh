#![allow(clippy::let_unit_value)] // for type inference
use hz_config::REDISIP;
use hz_ipc::connection::Encoding;
use redis::{Commands, Connection, ToRedisArgs};
use serde::{de::DeserializeOwned, Serialize};
use std::cell::RefCell;

pub const REDIS_CODING: Encoding = Encoding::Json;

thread_local! {
    pub static REDIS_R: RefCell<redis::Connection> = RefCell::new(create_connection());
}

pub fn hash2(s: &str) -> i32 {
    let mut res: i32 = 5381;
    for c in s.chars() {
        res = res.wrapping_mul(33).wrapping_add(c as i32);
    }
    res
}

pub fn redis_set<T, U>(conn: &mut Connection, key: T, value: U)
where
    T: Serialize + ToRedisArgs,
    U: Serialize,
{
    if REDIS_CODING == Encoding::Json {
        let redis_v = serde_json::to_string(&value).unwrap();
        let _: () = conn.set(key, redis_v).unwrap();
    } else {
        let redis_v = bincode::serialize(&value).unwrap();
        let _: () = conn.set(key, redis_v).unwrap();
    }
}

pub fn redis_get<T, U>(conn: &mut Connection, key: T) -> Option<U>
where
    T: Serialize + ToRedisArgs,
    U: DeserializeOwned,
{
    let res: Vec<u8> = conn.get(&key).unwrap();
    if res.is_empty() {
        return None;
    }
    let u: U = {
        if REDIS_CODING == Encoding::Json {
            serde_json::from_slice(&res).unwrap()
        } else {
            bincode::deserialize(&res).unwrap()
        }
    };
    Some(u)
}

pub fn create_connection() -> Connection {
    // info!("connecting to redis");
    let db =
        redis::Client::open(format!("redis://{REDISIP}:6379")).expect("Failed to connect to Redis");
    db.get_connection().expect("Failed to connect to Redis")
}

pub fn create_local_connection() -> Connection {
    // info!("connecting to redis");
    let db =
        redis::Client::open(format!("redis://localhost:6379")).expect("Failed to connect to Redis");
    db.get_connection().expect("Failed to connect to Redis")
}

pub async fn create_async_connection() -> redis::aio::Connection {
    // info!("connecting to redis");
    let db =
        redis::Client::open(format!("redis://{REDISIP}:6379")).expect("Failed to connect to Redis");
    db.get_async_connection()
        .await
        .expect("Failed to connect to Redis")
}
