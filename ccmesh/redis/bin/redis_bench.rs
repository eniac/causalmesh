use hz_config::*;
use hz_redis::helper::*;
use rustc_hash::FxHashMap as HashMap;
use tokio::net::TcpStream;
use tokio::sync::broadcast::{self, Sender};
use tokio::time::Instant;

type Handle = tokio::task::JoinHandle<i32>;
type HandleVec = Vec<Handle>;

pub async fn run_s(conn: &mut RedisConn) {
    let key = (rand::random::<usize>() % MAXKEY as usize).to_string();
    let m: M = M {
        key,
        value: "v1".to_string(),
        vc: Default::default(),
        deps: HashMap::default(),
    };
    conn.write_frame_and_flush(&m).await.unwrap();
}

pub async fn run(tx: Sender<()>) -> HandleVec {
    let mut handles: HandleVec = vec![];
    for _ in 0..5 {
        let mut rx = tx.subscribe();
        let h = tokio::spawn(async move {
            let mut counter = 0;
            let mut conn = RedisConn::new(
                0,
                TcpStream::connect(format!("{REDISIP}:28080"))
                    .await
                    .unwrap(),
                REDIS_CODING,
            );
            loop {
                tokio::select! {
                    _ = rx.recv() => {
                        break;
                    }
                    _ = run_s(&mut conn) => {
                        counter += 1;
                    }
                }
            }
            counter
        });
        handles.push(h);
    }
    handles
}

pub async fn collect(start: Instant, sender: Sender<()>, handles: HandleVec) {
    match tokio::signal::ctrl_c().await {
        Ok(()) => {
            sender.send(()).unwrap();
            let mut sum = 0;
            for h in handles {
                let r = h.await.unwrap();
                sum += r;
            }
            let dura = start.elapsed().as_millis() as f32;
            println!("Duration: {} ms", dura);
            println!("Count: {}", sum);
            println!("Throughput: {}", sum as f32 / (dura / 1000.0));
        }
        Err(err) => {
            panic!("{:?}", err);
        }
    }
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    tracing_subscriber::fmt::init();
    let (tx, _) = broadcast::channel::<()>(105);
    let start = Instant::now();
    let handles = run(tx.clone()).await;
    // println!("{:?}", run_s().await);
    collect(start, tx, handles).await;
}
