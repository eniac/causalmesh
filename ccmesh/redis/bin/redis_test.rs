use hz_config::*;
use hz_redis::helper::*;
use tokio::net::TcpStream;

#[tokio::main(flavor = "current_thread")]
async fn main() {
    let mut conn = RedisConn::new(
        0,
        TcpStream::connect(format!("{REDISIP}:28080"))
            .await
            .unwrap(),
        REDIS_CODING,
    );
    let s = serde_json::json!(
    {
        "key": "k1",
        "value": "v1",
        "vc": [2, 0],
        "deps": {
            "k2": [1, 2],
            "k3": [1, 2],
        }
    });
    let m: M = serde_json::from_value(s).unwrap();
    conn.write_frame_and_flush(&m).await.unwrap();
}
