use crate::mergeable::*;
use crate::vc::*;
use rustc_hash::FxHashMap as HashMap;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use std::hash::Hash;

pub trait MetaVCTrait: Debug + Eq + Hash + Default + VCTrait + Mergeable + Clone {}
impl<T> MetaVCTrait for T where T: Debug + Eq + Hash + Default + VCTrait + Mergeable + Clone {}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Meta<K, V, VC>
where
    K: Debug + Eq + Hash + Clone,
    VC: MetaVCTrait,
{
    pub key: K,
    pub value: V,
    pub vc: VC,
    pub deps: HashMap<K, VC>,
}

impl<K, V, VC> PartialEq for Meta<K, V, VC>
where
    K: Debug + Eq + Hash + Clone,
    VC: MetaVCTrait,
{
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key && self.vc == other.vc
    }
}

impl<K, V, VC> Eq for Meta<K, V, VC>
where
    K: Debug + Eq + Hash + Clone,
    VC: MetaVCTrait,
{
}

impl<K, V, VC> Hash for Meta<K, V, VC>
where
    K: Debug + Eq + Hash + Clone,
    VC: MetaVCTrait,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.key.hash(state);
        self.vc.hash(state);
    }
}

impl<K, V, VC> Meta<K, V, VC>
where
    K: Debug + Eq + Hash + Clone,
    VC: MetaVCTrait,
{
    pub fn new(key: K, value: V) -> Self {
        Meta {
            key,
            value,
            vc: VC::default(),
            deps: HashMap::default(),
        }
    }

    pub fn new_with_vc(key: K, value: V, vc: VC) -> Self {
        Meta {
            key,
            value,
            vc,
            deps: HashMap::default(),
        }
    }
}

impl<K, V, VC> Mergeable for Meta<K, V, VC>
where
    K: Debug + Eq + Hash + Clone,
    V: Clone,
    VC: MetaVCTrait,
{
    fn merge_into(&mut self, other: &Self) {
        debug_assert_eq!(self.key, other.key);
        if self.happens_before(other) || (self.concurrent(other) && other.privilege(self)) {
            self.value = other.value.clone();
        }
        self.vc.merge_into(&other.vc);
        self.deps.merge_into(&other.deps);
    }
}

impl<K, V, VC> MergeableNoDeps for Meta<K, V, VC>
where
    K: Debug + Eq + Hash + Clone,
    V: Clone,
    VC: MetaVCTrait,
{
    fn merge_into_no_deps(&mut self, other: &Self) {
        debug_assert_eq!(self.key, other.key);
        debug_assert!(self.deps.is_empty());
        if self.happens_before(other) || (self.concurrent(other) && other.privilege(self)) {
            self.value = other.value.clone();
        }
        self.vc.merge_into(&other.vc);
    }

    fn no_deps(&self) -> Self {
        Meta {
            key: self.key.clone(),
            value: self.value.clone(),
            vc: self.vc.clone(),
            deps: HashMap::default(),
        }
    }
}

// HOWTO: Trait forwarding
// deref would confuse Mergeable trait
impl<K, V, VC> VCTrait for Meta<K, V, VC>
where
    K: Debug + Eq + Hash + Clone,
    VC: MetaVCTrait,
{
    fn is_equal(&self, other: &Self) -> bool {
        self.vc.is_equal(&other.vc)
    }
    fn happens_before(&self, other: &Self) -> bool {
        self.vc.happens_before(&other.vc)
    }
    fn happens_after(&self, other: &Self) -> bool {
        other.happens_before(self)
    }
    fn concurrent(&self, other: &Self) -> bool {
        self.vc.concurrent(&other.vc)
    }
    fn privilege(&self, other: &Self) -> bool {
        self.vc.privilege(&other.vc)
    }
    fn increment(&mut self, idx: usize) {
        self.vc.increment(idx);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type Mi32 = Meta<i32, i32, DenseVC<2>>;
    type Mstr = Meta<String, String, SparseVC>;
    #[test]
    fn test1() {
        let mut a = Mi32::new(1, 2);
        a.increment(0);
        assert_eq!(a.vc, DenseVC([1, 0]));
        let mut b = Mi32::new(1, 1);
        b.increment(1);
        assert_eq!(b.vc, DenseVC([0, 1]));
        let c = a.merge(&b);
        assert_eq!(c.vc, DenseVC([1, 1]));
        assert_eq!(c.value, 2);
    }

    #[test]
    fn test2() {
        let mut a = Mstr::new(String::from("a"), String::from("a"));
        a.increment(0);
        assert_eq!(a.vc, DenseVC([1, 0]).to_sparse());
        let mut b = Mstr::new(String::from("a"), String::from("b"));
        b.increment(0);
        b.increment(1);
        assert_eq!(b.vc, DenseVC([1, 1]).to_sparse());
        let c = a.merge(&b);
        assert_eq!(c.vc, DenseVC([1, 1]).to_sparse());
        assert_eq!(c.value, String::from("b"));
    }

    #[test]
    fn test3() {
        let s1 = serde_json::json!(
            {
                "key": 1,
                "value": 1,
                "vc": [1, 0],
                "deps": {
                    "3": [1, 1]
                }
            }
        );
        let m1 = serde_json::from_value::<Mi32>(s1).unwrap();
        let s2 = serde_json::json!(
            {
                "key": 1,
                "value": 2,
                "vc": [2, 1],
                "deps": {
                    "3": [2, 0],
                    "4": [1, 1]
                }
            }
        );
        let m2 = serde_json::from_value::<Mi32>(s2).unwrap();
        let m3 = m1.merge(&m2);
        assert_eq!(m3.vc, DenseVC([2, 1]));
        assert_eq!(m3.value, 2);
        assert_eq!(m3.deps, {
            let mut deps = HashMap::default();
            deps.insert(3, DenseVC([2, 1]));
            deps.insert(4, DenseVC([1, 1]));
            deps
        });
    }
}
