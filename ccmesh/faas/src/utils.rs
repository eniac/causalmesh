use flashmap::{ReadGuard, ReadHandle, View, WriteGuard, WriteHandle};
use futures::StreamExt;
use hz_causal::*;
use hz_config::*;
use hz_redis::helper::*;
use rustc_hash::FxHashMap as HashMap;
use rustc_hash::FxHashSet as HashSet;
use std::collections::hash_map::Entry;
use std::collections::VecDeque;
use tokio::sync::mpsc::Receiver;
// use tracing::info;

pub type RHandle = ReadHandle<K, M>;
pub type WHandle = WriteHandle<K, M>;


#[tokio::main(flavor = "current_thread")]
pub async fn resolver(mut receiver: Receiver<HashSet<K>>, mut map_w: WHandle) {
    while let Some(mut todo) = receiver.recv().await {
        for key in todo.drain() {
            let mut todo = HashMap::default();
            REDIS_R.with(|conn| {
                let mut conn = conn.borrow_mut();
                let m: M = redis_get(&mut conn, key.clone()).unwrap();
                todo.insert(key.clone(), m);
            });
            let mut guard = map_w.guard();
            for (k, v) in todo.into_iter() {
                if let Some(m) = guard.get(&k) {
                    let m = m.merge(&v);
                    guard.insert(k, m);
                } else {
                    guard.insert(k, v);
                }
            }
        }
    }
}

#[tokio::main(flavor = "current_thread")]
pub async fn background(map_w: WHandle) {
    let mut pubsub = create_async_connection().await.into_pubsub();
    pubsub.subscribe("NEW").await.unwrap();
    let mut pubsub_stream = pubsub.on_message();
    let (to_resolver, from_bg) = tokio::sync::mpsc::channel(1);
    // let builder = std::thread::Builder::new().name("hz-server-resolver".into());
    // builder
    //     .spawn(move || {
    //         resolver(from_bg, map_w);
    //     })
    //     .unwrap();
    std::thread::spawn(move || {
        resolver(from_bg, map_w);
    });
    let mut todo = HashSet::default();
    let mut interval = tokio::time::interval(std::time::Duration::from_millis(50));
    loop {
        tokio::select! {
            Some(k) = pubsub_stream.next() => {
                let k: K = k.get_payload().unwrap();
                todo.insert(k);
            },
            _ = interval.tick() => {
                if to_resolver.capacity() > 0 && !todo.is_empty() {
                    let todo = std::mem::take(&mut todo);
                    to_resolver.send(todo).await.unwrap();
                }
            }
        }
    }
}
