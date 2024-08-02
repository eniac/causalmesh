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

pub type RHandle = ReadHandle<K, M>;
pub type WHandle = WriteHandle<K, M>;

pub fn retrieve_cut(
    read_guard: &View<ReadGuard<K, M>>,
    k: &String,
    rdag: &[String],
) -> HashMap<String, M> {
    let mut result: HashMap<String, M> = HashMap::default();
    let mut to_check = VecDeque::new();
    to_check.push_back(k.clone());
    result.insert(k.clone(), read_guard.get(k).unwrap().no_deps());
    let mut _counter = 0;
    while let Some(kk) = to_check.pop_front() {
        _counter += 1;
        let vj = read_guard.get(&kk).unwrap().clone();
        for dk in vj.deps.keys() {
            match result.entry(dk.clone()) {
                Entry::Occupied(_e) => {}
                Entry::Vacant(e) => {
                    e.insert(read_guard.get(dk).unwrap().no_deps());
                    to_check.push_back(dk.clone());
                }
            }
        }
    }
    result.retain(|k, _| rdag.contains(k));
    result
}

pub fn create_snapshot(
    read_guard: &View<ReadGuard<K, M>>,
    ri: &[String],
    rdag: &[String],
) -> HashMap<String, M> {
    let mut res: HashMap<String, M> = HashMap::default();
    for k in ri {
        let cut = retrieve_cut(read_guard, k, rdag);
        res.merge_into(&cut);
    }
    res
}

// pub fn retrieve_cut(map_r: &View<WriteGuard<K, M>>, k: K, rdag: &HashSet<K>) -> HashMap<K, VC> {
//     // let now = std::time::Instant::now();
//     let mut result: HashMap<K, VC> = HashMap::default();
//     let mut to_check = VecDeque::new();
//     to_check.push_back(k.clone());
//     let m = map_r.get(&k).unwrap();
//     // let vc = m.get_one().unwrap().vc.clone();
//     result.insert(k, m.vc.clone());
//     // let mut counter = 0;
//     while let Some(kk) = to_check.pop_front() {
//         // kk -> vj
//         // counter += 1;
//         let vj = map_r.get(&kk).unwrap();
//         for dk in vj.deps.keys() {
//             match result.entry(dk.clone()) {
//                 Entry::Occupied(_e) => {}
//                 Entry::Vacant(e) => {
//                     let vc = map_r.get(dk).unwrap().vc.clone();
//                     e.insert(vc);
//                     to_check.push_back(dk.clone());
//                 }
//             }
//         }
//     }
//     result.retain(|k, _| rdag.contains(k));
//     // info!("retrieve_cut: {:?}, takes {:?}", counter, now.elapsed());
//     result
// }

// pub fn create_snapshot(
//     map_r: &View<WriteGuard<K, M>>,
//     ri: &HashSet<K>,
//     rdag: &HashSet<K>,
// ) -> HashMap<K, VC> {
//     let mut res = HashMap::default();
//     for k in ri.iter() {
//         let cut = retrieve_cut(map_r, k.clone(), rdag);
//         res.merge_into(&cut);
//     }
//     res
// }

pub fn is_covered(
    meta: M,
    t: &mut HashMap<K, Vec<M>>,
    map_r: &View<WriteGuard<K, M>>,
    conn: &mut redis::Connection,
) -> bool {
    // if map_r.contains_key(&meta.key) && map_r.get(&meta.key).unwrap().get_one().unwrap().vc >= meta.vc {
    //     return true;
    // }
    for (k_, vc_) in meta.deps.iter() {
        if let Some(m) = map_r.get(k_) {
            if m.vc >= *vc_ {
                continue;
            }
        }
        if t.contains_key(k_) {
            let mut ok = false;
            for m_ in t.get(k_).unwrap() {
                if m_.vc >= *vc_ {
                    ok = true;
                    break;
                }
            }
            if ok {
                continue;
            }
        }
        let m: M = redis_get(conn, k_).unwrap();
        match t.entry(k_.clone()) {
            Entry::Occupied(mut e) => {
                e.get_mut().push(m.clone());
            }
            Entry::Vacant(e) => {
                e.insert(vec![m.clone()]);
            }
        }
        if is_covered(m, t, map_r, conn) {
            continue;
        }
        panic!("unreachable");
    }
    true
}

pub fn resolve(map_w: &mut WHandle, todo: HashSet<K>) -> HashSet<K> {
    // let mut rest = HashSet::default();
    let mut counter = 0;
    let mut done = HashSet::default();
    let mut rest = todo.clone();
    // let mut reader_conn = create_connection();
    REDIS_R.with(|conn| {
    for k in todo {
        if done.contains(&k) {
            continue;
        }
        let m: M = redis_get(&mut conn.borrow_mut(), k.clone())
            .unwrap_or_else(|| panic!("getting {:?} failed", k));
        let mut t: HashMap<K, Vec<M>> = HashMap::default();
        t.insert(k.clone(), vec![m.clone()]);
        let mut guard = map_w.guard();
        let covered = is_covered(m, &mut t, &guard, &mut conn.borrow_mut());
        if covered {
            for (k_, metas) in t.iter() {
                let mut meta = metas[0].clone();
                for m_ in metas {
                    meta.merge_into(m_);
                }
                if guard.contains_key(k_) {
                    guard.replace(k_.clone(), |old| {
                        let mut m = old.clone();
                        m.merge_into(&meta);
                        m
                    });
                } else {
                    guard.insert(k_.clone(), meta);
                }
                rest.remove(k_);
            }
            guard.publish();
            rest.remove(&k);
            done.insert(k);
            counter += 1;
            if counter >= 10 {
                break;
            }
        } else {
            // rest.insert(k.clone());
        }
    }
    });
    rest
}

#[tokio::main(flavor = "current_thread")]
pub async fn resolver(mut receiver: Receiver<HashSet<K>>, mut map_w: WHandle) {
    let mut rest = HashSet::default();
    loop {
        while let Some(mut todo) = receiver.recv().await {
            todo.extend(rest);
            rest = resolve(&mut map_w, todo);
        }
    }
}
#[tokio::main(flavor = "current_thread")]
pub async fn background(map_w: WHandle) {
    let mut pubsub = create_async_connection().await.into_pubsub();
    pubsub.subscribe("NEW").await.unwrap();
    let mut pubsub_stream = pubsub.on_message();
    let (to_resolver, from_bg) = tokio::sync::mpsc::channel(1);
    let builder = std::thread::Builder::new().name("hz-server-resolver".into());
    builder
        .spawn(move || {
            resolver(from_bg, map_w);
        })
        .unwrap();
    // std::thread::spawn(move || {
    //     resolver(from_bg, map_w);
    // });
    let mut todo = HashSet::default();
    let mut interval = tokio::time::interval(std::time::Duration::from_millis(100));
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
