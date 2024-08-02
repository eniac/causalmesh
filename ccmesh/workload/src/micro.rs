use hz_config::*;
use rand::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Op {
    R(String),
    W(String, String),
    M,
}

// #[derive(Debug, Clone, Default, Serialize, Deserialize)]
// pub struct Workload(pub Vec<Op>);
pub type Workload = Vec<Op>;

#[derive(Default, Debug)]
pub struct WorkloadBuilder {
    pub delay_writes: bool,
    pub nw: i32,
    pub nr: i32,
    pub nm: i32,
    pub rng: ThreadRng,
    pub zipf: Option<zipf::ZipfDistribution>,
    pub uniform: Option<rand::distributions::Uniform<i32>>,
}

impl WorkloadBuilder {
    pub fn n10m1(self) -> Self {
        self.num_read(6).num_write(4).num_migrate(1)
    }

    pub fn num_write(mut self, nw: i32) -> Self {
        self.nw = nw;
        self
    }

    pub fn num_read(mut self, nr: i32) -> Self {
        self.nr = nr;
        self
    }

    pub fn num_migrate(mut self, nm: i32) -> Self {
        self.nm = nm;
        self
    }

    pub fn zipf(mut self, a: f64) -> Self {
        assert!(self.uniform.is_none(), "sample already set");
        let _ = self
            .zipf
            .insert(zipf::ZipfDistribution::new(MAXKEY as usize, a).unwrap());
        self
    }

    pub fn uniform(mut self) -> Self {
        assert!(self.zipf.is_none(), "sample already set");
        let _ = self
            .uniform
            .insert(rand::distributions::Uniform::new(0, MAXKEY));
        self
    }

    pub fn sample_int(&mut self) -> i32 {
        if let Some(zipf) = &self.zipf {
            zipf.sample(&mut self.rng) as i32 - 1
        } else if let Some(uniform) = &self.uniform {
            uniform.sample(&mut self.rng)
        } else {
            panic!("no sample set");
        }
    }

    pub fn sample(&mut self) -> String {
        self.sample_int().to_string()
    }

    pub fn delay_writes(mut self) -> Self {
        self.delay_writes = true;
        self
    }

    pub fn build(&mut self) -> Workload {
        assert!(self.nr + self.nw + self.nm > 0, "num must be positive");
        let mut ops = vec![];
        for _ in 0..self.nr {
            ops.push(Op::R(self.sample()));
        }
        for _ in 0..self.nm {
            ops.push(Op::M);
        }
        if self.delay_writes {
            ops.shuffle(&mut self.rng);
            for _ in 0..self.nw {
                ops.push(Op::W(self.sample(), format!("{:0>8}", self.sample())));
            }
        } else {
            for _ in 0..self.nw {
                ops.push(Op::W(self.sample(), format!("{:0>8}", self.sample())));
            }
            ops.shuffle(&mut self.rng);
        }
        ops
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test1() {
        let mut builder = WorkloadBuilder::default().n10m1().zipf(1.0).delay_writes();
        let workload = builder.build();
        let mut writing = false;
        assert_eq!(workload.len(), 11);
        for op in &workload {
            match op {
                Op::R(_) => {
                    assert!(!writing)
                }
                Op::W(_, _) => {
                    writing = true;
                }
                Op::M => {
                    assert!(!writing)
                }
            }
        }
    }
}
