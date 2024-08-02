use hz_causal::*;
use hz_config::*;
use hz_ipc::connection::Connection;
use hz_redis::helper::*;
use redis::Commands;
use std::cell::RefCell;
use tokio::net::{TcpListener, TcpStream};

type M = Meta<String, String, DenseVC<T>>;
pub type RedisConn = Connection<M, TcpStream, 512>;

thread_local! {
    pub static REDIS_CONN: RefCell<redis::Connection> = RefCell::new(create_connection());
}

async fn process(mut conn: RedisConn) {
    while let Some(mut m) = conn.read_frame().await.unwrap() {
        REDIS_CONN.with(|conn| {
            // if (MODE == "opt" || MODE == "con") && MEDIA {
            if MODE == "opt" || MODE == "con" {
                m.deps.retain(|_, vc| !(vc == &VC::default()));
            }
            let key = m.key.clone();
            let m2: Option<M> = redis_get(&mut conn.borrow_mut(), &m.key);
            if let Some(mut m2) = m2 {
                m2.merge_into(&m);
                redis_set(&mut conn.borrow_mut(), m.key, m2);
            } else {
                redis_set(&mut conn.borrow_mut(), m.key.clone(), m);
            }
            if MODE == "opt" || MODE == "con" || MODE == "faas" {
                REDIS_R.with(|conn| {
                    let _res: () = conn.borrow_mut().publish("NEW", key).unwrap();
                });
            }
        });
        // conn.write_frame_and_flush(&m).await.unwrap();
    }
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    let listener = TcpListener::bind(format!("{REDISIP}:28080")).await.unwrap();
    while let Ok((socket, _)) = listener.accept().await {
        let conn = RedisConn::new(0, socket, REDIS_CODING);
        tokio::spawn(async move {
            process(conn).await;
        });
    }
}
