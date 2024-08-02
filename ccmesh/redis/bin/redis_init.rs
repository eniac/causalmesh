use hz_config::*;
use hz_redis::helper::*;

#[tokio::main(flavor = "current_thread")]
async fn main() {
    let mut conn = create_connection();
    for i in 0..MAXKEY {
        let key = format!("{}", i);
        let val = format!("{}", i);
        redis_set(&mut conn, key, val);
    }
}
