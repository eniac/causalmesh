#![allow(clippy::format_push_string)]
use hz_causal::*;
use rustc_hash::FxHashMap as HashMap;

type VC = DenseVC<3>;
type M = Meta<String, String, DenseVC<3>>;

#[allow(dead_code)]
type Black = HashMap<String, Vec<M>>;
type White = HashMap<String, M>;

trait Tla {
    fn to_tla(&self) -> String;
}

impl Tla for VC {
    fn to_tla(&self) -> String {
        format!("<<{}, {}, {}>>", self.0[0], self.0[1], self.0[2])
    }
}

impl<T> Tla for HashMap<String, T>
where
    T: Tla,
{
    fn to_tla(&self) -> String {
        if self.is_empty() {
            "<<>>".into()
        } else {
            let mut s = String::new();
            s.push('[');
            let mut keys = self.keys().collect::<Vec<_>>();
            keys.sort_unstable();
            for k in keys {
                s.push_str(&format!("{} |-> {}, ", k, self[k].to_tla()));
            }
            s.pop();
            s.pop();
            s.push(']');
            s
        }
    }
}

impl<T> Tla for Vec<T>
where
    T: Tla,
{
    fn to_tla(&self) -> String {
        if self.is_empty() {
            "{}".into()
        } else {
            let mut s = String::new();
            s.push('{');
            for v in self {
                s.push_str(&format!("{}, ", v.to_tla()));
            }
            s.pop();
            s.pop();
            s.push('}');
            s
        }
    }
}

impl Tla for M {
    fn to_tla(&self) -> String {
        format!(
            "[key |-> \"{}\", vc |-> {}, deps |-> {}]",
            self.key,
            self.vc.to_tla(),
            self.deps.to_tla()
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tla1() {
        let vc: DenseVC<3> = [1, 2, 3].into();
        assert_eq!(vc.to_tla(), "<<1, 2, 3>>");
    }

    #[test]
    fn tla2() {
        let mut deps: HashMap<String, DenseVC<3>> = HashMap::default();
        deps.insert("a".into(), [1, 2, 3].into());
        deps.insert("b".into(), [4, 5, 6].into());
        assert_eq!(deps.to_tla(), "[a |-> <<1, 2, 3>>, b |-> <<4, 5, 6>>]");
    }

    #[test]
    fn tla3() {
        let s = serde_json::json!(
        {
            "a": {
                "key": "a",
                "value": "a",
                "vc": [3, 1, 0],
                "deps": {}
            },
            "b": {
                "key": "b",
                "value": "a",
                "vc": [0, 0, 0],
                "deps": {
                    "a": [3, 1, 0]
                }
            },
        });
        let white: White = serde_json::from_value(s).unwrap();
        assert_eq!(
            white.to_tla(),
            "[a |-> [key |-> \"a\", vc |-> <<3, 1, 0>>, deps |-> <<>>], b |-> [key |-> \"b\", vc |-> <<0, 0, 0>>, deps |-> [a |-> <<3, 1, 0>>]]]"
        );
    }

    #[test]
    fn tla4() {
        let s = serde_json::json!(
        {
            "a": [{
                "key": "a",
                "value": "a",
                "vc": [3, 1, 0],
                "deps": {
                    "b": [0, 0, 0]
                }
            }],
            "b": [{
                "key": "b",
                "value": "b",
                "vc": [0, 0, 0],
                "deps": {}
            },
            {
                "key": "b",
                "value": "b",
                "vc": [1, 0, 0],
                "deps": {
                    "a": [3, 1, 0],
                    "b": [0, 0, 0]
                }
            }],
        });
        let black: Black = serde_json::from_value(s).unwrap();
        assert_eq!(
            black.to_tla(),
            "[a |-> {[key |-> \"a\", vc |-> <<3, 1, 0>>, deps |-> [b |-> <<0, 0, 0>>]]}, b |-> {[key |-> \"b\", vc |-> <<0, 0, 0>>, deps |-> <<>>], [key |-> \"b\", vc |-> <<1, 0, 0>>, deps |-> [a |-> <<3, 1, 0>>, b |-> <<0, 0, 0>>]]}]"
        );
    }
}

pub fn main() {
    let s = serde_json::json!(
    {
        "k1": [{
            "key": "k1",
            "value": "a",
            "vc": [2, 2, 0],
            "deps": {
                "k2": [0, 1, 0],
                "k3": [0, 0, 0]
            }
        }],
        "k2": [{
            "key": "k2",
            "value": "b",
            "vc": [0, 1, 0],
            "deps": {
                "k3": [0, 0, 1]
            }
        }, {
            "key": "k2",
            "value": "b",
            "vc": [1, 0, 0],
            "deps": {}
        }],
        "k3": [{
            "key": "k3",
            "value": "c",
            "vc": [0, 0, 0],
            "deps": {}
        }, {
            "key": "k3",
            "value": "c",
            "vc": [0, 0, 1],
            "deps": {}
        }]
    });
    let black: Black = serde_json::from_value(s).unwrap();
    println!("{}", black.to_tla());

    let s = serde_json::json!(
    {
        "k1": {
            "key": "k1",
            "value": "a",
            "vc": [3, 1, 0],
            "deps": {}
        },
        "k2": {
            "key": "k2",
            "value": "b",
            "vc": [0, 0, 0],
            "deps": {}
        },
        "k3": {
            "key": "k3",
            "value": "c",
            "vc": [0, 0, 0],
            "deps": {}
        }
    });
    let white: White = serde_json::from_value(s).unwrap();
    println!("{}", white.to_tla());
}
