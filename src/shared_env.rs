use bitvec::prelude::*;
use std::iter::{self, once};

#[derive(Debug)]
pub struct SharedEnvironment {
  shared_bits: BitVec<usize, Lsb0>,
  offsets: Vec<usize>, // offsets[i] = start of node i
}

impl SharedEnvironment {
  fn new(node_sorts: Vec<usize>) -> Self {
    let offsets = once(&0usize)
      .chain(once(&0usize))
      .chain(node_sorts.iter())
      .scan(0usize, |state, &x| {
        *state = *state + x;
        Some(*state)
      })
      .collect::<Vec<_>>();
    let shared_bits = BitVec::repeat(false, *offsets.last().unwrap());
    SharedEnvironment {
      shared_bits,
      offsets,
    }
  }

  fn set(&mut self, idx: usize, value: &BitSlice) {
    self.shared_bits[self.offsets[idx]..self.offsets[idx + 1]].copy_from_bitslice(value);
  }

  fn get(&mut self, idx: usize) -> &BitSlice {
    &self.shared_bits[self.offsets[idx]..self.offsets[idx + 1]]
  }

  pub fn not(&self, i1: usize) -> &BitSlice {
    let s1 = self.get(i1);
    !s1
  }

  pub fn and(&self, i1: usize, i2: usize) -> &BitSlice {
    let s1 = self.get(i1);
    let s2 = self.get(i2);
    s1 & s2
  }

  pub fn nand(&self, i1: usize, i2: usize) -> &BitSlice {
    let s1 = self.get(i1);
    let s2 = self.get(i2);
    !(s1 & s2)
  }

  pub fn nor(&self, i1: usize, i2: usize) -> &BitSlice {
    let s1 = self.get(i1);
    let s2 = self.get(i2);
    !(s1 | s2)
  }

  pub fn or(&self, i1: usize, i2: usize) -> &BitSlice {
    let s1 = self.get(i1);
    let s2 = self.get(i2);
    s1 | s2
  }

  pub fn xnor(&self, i1: usize, i2: usize) -> &BitSlice {
    let s1 = self.get(i1);
    let s2 = self.get(i2);
    !(s1 ^ s2)
  }

  pub fn xor(&self, i1: usize, i2: usize) -> &BitSlice {
    let s1 = self.get(i1);
    let s2 = self.get(i2);
    s1 ^ s2
  }

  pub fn slice(&self, i1: usize, l: usize, u: usize) -> &BitSlice {
    let s1 = self.get(i1);
    &s1[l..(u+1)]
  }

  pub fn cat(&self, i1: usize, i2: usize) -> &BitSlice {
    let s1 = self.get(i1);
    let s2 = self.get(i2);
    [s1, s2].concat()
  }


}



#[cfg(test)]
mod tests {

  use super::*;

  #[test]
  fn test_get_set() {
    let node_widths = vec![2, 8, 6];
    let mut s_env = SharedEnvironment::new(node_widths);
    assert!(s_env.get(1) == bits![0, 0]);
    assert!(s_env.get(2) == bits![0, 0, 0, 0, 0, 0, 0, 0]);
    assert!(s_env.get(3) == bits![0, 0, 0, 0, 0, 0]);

    s_env.set(1, bits![0, 1]);
    s_env.set(2, bits![0, 1, 0, 1, 1, 1, 1, 1]);
    s_env.set(3, bits![0, 1, 0, 0, 0, 0]);

    assert!(s_env.get(1) == bits![0, 1]);
    assert!(s_env.get(2) == bits![0, 1, 0, 1, 1, 1, 1, 1]);
    assert!(s_env.get(3) == bits![0, 1, 0, 0, 0, 0]);
  }
}
