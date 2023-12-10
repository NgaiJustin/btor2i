use num_traits::{One, Zero};
use std::{
  cmp::Ordering,
  convert::From,
  fmt::Display,
  ops::{Add, Mul, Neg},
};

use bitvec::prelude::*;
use num_bigint::{BigInt, BigUint};
use std::{
  iter::{self, once},
  ops::BitXorAssign,
};

#[derive(Debug)]
pub struct SharedEnvironment {
  shared_bits: BitVec<usize, Lsb0>, // RI: integers are little-endian
  offsets: Vec<usize>,              // offsets[i] = start of node i
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

  pub fn sext(&mut self, i1: usize, i2: usize) -> () {
    let old_start = self.offsets[i1];
    let old_end = self.offsets[i1 + 1];
    let new_start = self.offsets[i2];
    let new_end = self.offsets[i2 + 1];
    let first_bit = self.shared_bits[old_start];
    self.shared_bits.copy_within(old_start..old_end, new_start);
    self.shared_bits[new_start + (old_end - old_start)..new_end].fill(first_bit);
  }

  pub fn uext(&mut self, i1: usize, i2: usize) -> () {
    let old_start = self.offsets[i1];
    let old_end = self.offsets[i1 + 1];
    let new_start = self.offsets[i2];
    let new_end = self.offsets[i2 + 1];
    self.shared_bits.copy_within(old_start..old_end, new_start);
    self.shared_bits[new_start + (old_end - old_start)..new_end].fill(false);
  }

  pub fn slice(&mut self, u: usize, l: usize, i1: usize, i2: usize) {
    let old_start = self.offsets[i1];
    let new_start = self.offsets[i2];
    self
      .shared_bits
      .copy_within(old_start + l..old_start + u + 1, new_start);
  }

  pub fn not(&mut self, i1: usize, i2: usize) {
    let old_start = self.offsets[i1];
    let old_end = self.offsets[i1 + 1];
    let new_start = self.offsets[i2];
    let new_end = self.offsets[i2 + 1];
    let mut rhs = BitVec::repeat(false, old_end - old_start);
    rhs ^= &self.shared_bits[old_start..old_end];
    self.shared_bits[new_start..new_end].copy_from_bitslice(rhs.as_bitslice());
  }

  pub fn and(&mut self, i1: usize, i2: usize, i3: usize) {
    let mut rhs = BitVec::from_bitslice(&self.shared_bits[self.offsets[i1]..self.offsets[i1 + 1]]);
    rhs &= &self.shared_bits[self.offsets[i2]..self.offsets[i2 + 1]];
    self.shared_bits[self.offsets[i3]..self.offsets[i3 + 1]].copy_from_bitslice(rhs.as_bitslice());
  }

  pub fn nand(&mut self, i1: usize, i2: usize, i3: usize) {
    let mut rhs = BitVec::from_bitslice(&self.shared_bits[self.offsets[i1]..self.offsets[i1 + 1]]);
    rhs &= &self.shared_bits[self.offsets[i2]..self.offsets[i2 + 1]];
    rhs = !rhs;
    self.shared_bits[self.offsets[i3]..self.offsets[i3 + 1]].copy_from_bitslice(rhs.as_bitslice());
  }

  pub fn nor(&mut self, i1: usize, i2: usize, i3: usize) {
    let mut rhs = BitVec::from_bitslice(&self.shared_bits[self.offsets[i1]..self.offsets[i1 + 1]]);
    rhs |= &self.shared_bits[self.offsets[i2]..self.offsets[i2 + 1]];
    rhs = !rhs;
    self.shared_bits[self.offsets[i3]..self.offsets[i3 + 1]].copy_from_bitslice(rhs.as_bitslice());
  }

  pub fn or(&mut self, i1: usize, i2: usize, i3: usize) {
    let mut rhs = BitVec::from_bitslice(&self.shared_bits[self.offsets[i1]..self.offsets[i1 + 1]]);
    rhs |= &self.shared_bits[self.offsets[i2]..self.offsets[i2 + 1]];
    self.shared_bits[self.offsets[i3]..self.offsets[i3 + 1]].copy_from_bitslice(rhs.as_bitslice());
  }

  pub fn xnor(&mut self, i1: usize, i2: usize, i3: usize) {
    let mut rhs = BitVec::from_bitslice(&self.shared_bits[self.offsets[i1]..self.offsets[i1 + 1]]);
    rhs ^= &self.shared_bits[self.offsets[i2]..self.offsets[i2 + 1]];
    rhs = !rhs;
    self.shared_bits[self.offsets[i3]..self.offsets[i3 + 1]].copy_from_bitslice(rhs.as_bitslice());
  }

  pub fn xor(&mut self, i1: usize, i2: usize, i3: usize) {
    let mut rhs = BitVec::from_bitslice(&self.shared_bits[self.offsets[i1]..self.offsets[i1 + 1]]);
    rhs ^= &self.shared_bits[self.offsets[i2]..self.offsets[i2 + 1]];
    self.shared_bits[self.offsets[i3]..self.offsets[i3 + 1]].copy_from_bitslice(rhs.as_bitslice());
  }

  pub fn concat(&mut self, i1: usize, i2: usize, i3: usize) {
    let start1 = self.offsets[i1];
    let end1 = self.offsets[i1 + 1];
    let start2 = self.offsets[i2];
    let end2 = self.offsets[i2 + 1];
    let start3 = self.offsets[i3];
    self.shared_bits.copy_within(start1..end1, start3);
    self
      .shared_bits
      .copy_within(start2..end2, start3 + end1 - start1);
  }

  fn slice_to_bigint(slice: &BitSlice) -> BigInt {
    if slice.is_empty() {
      Zero::zero()
    } else if slice[slice.len() - 1] {
      let z: BigInt = Zero::zero();
      let o: BigInt = One::one();
      let mut ans = z - o;
      for i in 0..slice.len() {
        ans.set_bit(i.try_into().unwrap(), slice[i])
      }
      ans
    } else {
      let mut ans: BigInt = Zero::zero();
      for i in 0..slice.len() {
        ans.set_bit(i.try_into().unwrap(), slice[i])
      }
      ans
    }
  }

  fn slice_to_biguint(slice: &BitSlice) -> BigUint {
    let mut ans: BigUint = Zero::zero();
    for i in 0..slice.len() {
      ans.set_bit(i.try_into().unwrap(), slice[i])
    }
    return ans;
  }

  pub fn inc(&mut self, i1: usize, i2: usize) {
    self
      .shared_bits
      .copy_within(self.offsets[i1]..self.offsets[i1 + 1], self.offsets[i2]);
    let dest = self.shared_bits[self.offsets[i2]..self.offsets[i2 + 1]].as_mut();
    match (dest.first_zero()) {
      Some(i) => {
        dest[i..i + 1].fill(true);
        dest[..i].fill(false);
      }
      None => {
        dest.fill(false);
      }
    }
  }

  pub fn dec(&mut self, i1: usize, i2: usize) {
    self
      .shared_bits
      .copy_within(self.offsets[i1]..self.offsets[i1 + 1], self.offsets[i2]);
    let dest = self.shared_bits[self.offsets[i2]..self.offsets[i2 + 1]].as_mut();
    match (dest.first_one()) {
      Some(i) => {
        dest[i..i + 1].fill(false);
        dest[..i].fill(true);
      }
      None => {
        dest.fill(true);
      }
    }
  }

  pub fn neg(&mut self, i1: usize, i2: usize) {
    let bitwise_neg =
      !BitVec::from_bitslice(&self.shared_bits[self.offsets[i1]..self.offsets[i1 + 1]]);
    let dest = self.shared_bits[self.offsets[i2]..self.offsets[i2 + 1]].as_mut();
    dest.copy_from_bitslice(&bitwise_neg);

    match (dest.first_zero()) {
      Some(i) => {
        dest[i..i + 1].fill(true);
        dest[..i].fill(false);
      }
      None => {
        dest.fill(false);
      }
    }
  }

  pub fn redand(&mut self, i1: usize, i2: usize) {
    let ans = self.shared_bits[self.offsets[i1]..self.offsets[i1 + 1]].all();
    self.shared_bits[self.offsets[i2]..self.offsets[i2] + 1].fill(ans);
  }

  pub fn redor(&mut self, i1: usize, i2: usize) {
    let ans = self.shared_bits[self.offsets[i1]..self.offsets[i1 + 1]].any();
    self.shared_bits[self.offsets[i2]..self.offsets[i2] + 1].fill(ans);
  }

  pub fn redxor(&mut self, i1: usize, i2: usize) {
    let ans = self.shared_bits[self.offsets[i1]..self.offsets[i1 + 1]].count_ones() % 2 == 1;
    self.shared_bits[self.offsets[i2]..self.offsets[i2] + 1].fill(ans);
  }

  pub fn iff(&mut self, i1: usize, i2: usize, i3: usize) {
    let ans = self.shared_bits[self.offsets[i1]] == self.shared_bits[self.offsets[i2]];
    self.shared_bits[self.offsets[i3]..self.offsets[i3] + 1].fill(ans);
  }

  pub fn implies(&mut self, i1: usize, i2: usize, i3: usize) {
    let ans = !self.shared_bits[self.offsets[i1]] || self.shared_bits[self.offsets[i2]];
    self.shared_bits[self.offsets[i3]..self.offsets[i3] + 1].fill(ans);
  }

  pub fn eq(&mut self, i1: usize, i2: usize, i3: usize) {
    let ans = self.shared_bits[self.offsets[i1]..self.offsets[i1 + 1]]
      == self.shared_bits[self.offsets[i2]..self.offsets[i2 + 1]];
    self.shared_bits[self.offsets[i3]..self.offsets[i3] + 1].fill(ans);
  }

  pub fn neq(&mut self, i1: usize, i2: usize, i3: usize) {
    let ans = self.shared_bits[self.offsets[i1]..self.offsets[i1 + 1]]
      != self.shared_bits[self.offsets[i2]..self.offsets[i2 + 1]];
    self.shared_bits[self.offsets[i3]..self.offsets[i3] + 1].fill(ans);
  }

  fn compare_signed(&self, i1: usize, i2: usize) -> Ordering {
    let a = Self::slice_to_bigint(&self.shared_bits[self.offsets[i1]..self.offsets[i1 + 1]]);
    let b = Self::slice_to_bigint(&self.shared_bits[self.offsets[i2]..self.offsets[i2 + 1]]);
    a.cmp(&b)
  }

  fn compare_unsigned(&self, i1: usize, i2: usize) -> Ordering {
    let a = &self.shared_bits[self.offsets[i1]..self.offsets[i1 + 1]];
    let b = &self.shared_bits[self.offsets[i2]..self.offsets[i2 + 1]];
    a.cmp(&b)
  }

  pub fn sgt(&mut self, i1: usize, i2: usize, i3: usize) {
    let ans = match self.compare_signed(i1, i2) {
      Ordering::Less => false,
      Ordering::Equal => false,
      Ordering::Greater => true,
    };
    self.shared_bits[self.offsets[i3]..self.offsets[i3] + 1].fill(ans);
  }

  pub fn ugt(&mut self, i1: usize, i2: usize, i3: usize) {
    let ans = match self.compare_unsigned(i1, i2) {
      Ordering::Less => false,
      Ordering::Equal => false,
      Ordering::Greater => true,
    };
    self.shared_bits[self.offsets[i3]..self.offsets[i3] + 1].fill(ans);
  }

  pub fn sgte(&mut self, i1: usize, i2: usize, i3: usize) {
    let ans = match self.compare_signed(i1, i2) {
      Ordering::Less => false,
      Ordering::Equal => true,
      Ordering::Greater => true,
    };
    self.shared_bits[self.offsets[i3]..self.offsets[i3] + 1].fill(ans);
  }

  pub fn ugte(&mut self, i1: usize, i2: usize, i3: usize) {
    let ans = match self.compare_unsigned(i1, i2) {
      Ordering::Less => false,
      Ordering::Equal => true,
      Ordering::Greater => true,
    };
    self.shared_bits[self.offsets[i3]..self.offsets[i3] + 1].fill(ans);
  }

  pub fn slt(&mut self, i1: usize, i2: usize, i3: usize) {
    let ans = match self.compare_signed(i1, i2) {
      Ordering::Greater => false,
      Ordering::Equal => false,
      Ordering::Less => true,
    };
    self.shared_bits[self.offsets[i3]..self.offsets[i3] + 1].fill(ans);
  }

  pub fn ult(&mut self, i1: usize, i2: usize, i3: usize) {
    let ans = match self.compare_unsigned(i1, i2) {
      Ordering::Greater => false,
      Ordering::Equal => false,
      Ordering::Less => true,
    };
    self.shared_bits[self.offsets[i3]..self.offsets[i3] + 1].fill(ans);
  }

  pub fn slte(&mut self, i1: usize, i2: usize, i3: usize) {
    let ans = match self.compare_signed(i1, i2) {
      Ordering::Greater => false,
      Ordering::Equal => true,
      Ordering::Less => true,
    };
    self.shared_bits[self.offsets[i3]..self.offsets[i3] + 1].fill(ans);
  }

  pub fn ulte(&mut self, i1: usize, i2: usize, i3: usize) {
    let ans = match self.compare_unsigned(i1, i2) {
      Ordering::Greater => false,
      Ordering::Equal => true,
      Ordering::Less => true,
    };
    self.shared_bits[self.offsets[i3]..self.offsets[i3] + 1].fill(ans);
  }

  //   pub fn ro
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
