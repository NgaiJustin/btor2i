use std::{
  convert::From,
  fmt::Display,
  ops::{Add, Mul, Neg},
};

use bitvec::prelude::*;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

#[derive(Debug, Clone)]
pub struct BitVector {
  bits: BitVec<usize, Lsb0>,
}

impl BitVector {
  /// the value 0, of width `len`
  pub fn zeros(len: usize) -> Self {
    let mut bits = BitVec::new();
    for _ in 0..len {
      bits.push(false);
    }
    BitVector { bits }
  }

  /// the value 1, of width `len`
  pub fn one(len: usize) -> Self {
    BitVector::inc(&BitVector::zeros(len))
  }

  /// the value -1, of width `len`
  pub fn ones(len: usize) -> Self {
    let mut bits = BitVec::new();
    for _ in 0..len {
      bits.push(true);
    }
    BitVector { bits }
  }

  /// sign-extend `bv` by `w` bits
  pub fn sign_extend(bv: &BitVector, w: usize) -> Self {
    let mut other_vec = BitVec::new();
    for bit in bv.bits.iter() {
      other_vec.push(*bit);
    }
    for _ in bv.bits.len()..bv.bits.len() + w {
      other_vec.push(*bv.bits.last().as_deref().unwrap());
    }
    BitVector { bits: other_vec }
  }

  /// zero-extend `bv` by `w`
  pub fn zero_extend(bv: &BitVector, w: usize) -> Self {
    let mut other_vec = BitVec::new();
    for bit in bv.bits.iter() {
      other_vec.push(*bit);
    }
    for _ in 0..w {
      other_vec.push(false);
    }
    BitVector { bits: other_vec }
  }

  /// keep bits `l` thru `u` (inclusive, 1-indexed) of `bv`
  pub fn slice(bv: &BitVector, l: usize, u: usize) -> Self {
    let mut other_vec = BitVec::new();
    for i in (l - 1)..u {
      other_vec.push(bv.bits[i]);
    }

    BitVector { bits: other_vec }
  }

  /// bitwise not
  pub fn not(bv: &BitVector) -> Self {
    let bits = bv.bits.clone();
    BitVector { bits: !bits }
  }

  /// increment
  pub fn inc(bv: &BitVector) -> Self {
    let mut missing: usize = 0;
    while missing < bv.bits.len() && bv.bits[missing] {
      missing += 1
    }
    if missing == bv.bits.len() {
      BitVector::zeros(bv.bits.len())
    } else {
      let mut ans = bv.clone();
      ans.bits.set(missing, true);
      for i in 0..missing {
        ans.bits.set(i, false);
      }
      ans
    }
  }

  /// decrement
  pub fn dec(bv: &BitVector) -> Self {
    let mut present: usize = 0;
    while present < bv.bits.len() && !bv.bits[present] {
      present += 1
    }
    if present == bv.bits.len() {
      BitVector::ones(bv.bits.len())
    } else {
      let mut ans = bv.clone();
      ans.bits.set(present, false);
      for i in 0..present {
        ans.bits.set(i, true);
      }
      ans
    }
  }

  /// two's complement negation
  pub fn neg(bv: &BitVector) -> Self {
    BitVector::inc(&BitVector::not(bv))
  }

  pub fn redand(bv: &BitVector) -> bool {
    bv.bits.all()
  }

  pub fn redor(bv: &BitVector) -> bool {
    bv.bits.any()
  }

  pub fn redxor(bv: &BitVector) -> bool {
    bv.bits.count_ones() % 2 == 1
  }

  pub fn iff(bv1: &BitVector, bv2: &BitVector) -> bool {
    bv1.bits.any() == bv2.bits.any()
  }

  pub fn implies(bv1: &BitVector, bv2: &BitVector) -> bool {
    bv2.bits.any() | (!bv1.bits.any())
  }

  pub fn equals(bv1: &BitVector, bv2: &BitVector) -> bool {
    if bv1.bits.count_ones() != bv2.bits.count_ones() {
      return false;
    }
    for i in bv1.bits.iter_ones() {
      if !(bv2.bits[i]) {
        return false;
      }
    }
    bv1.bits.len() == bv2.bits.len()
  }

  pub fn neq(bv1: &BitVector, bv2: &BitVector) -> bool {
    !BitVector::equals(bv1, bv2)
  }

  // a more intelligent implementation of this would be
  // to construct the vector of bytes and pass that to from_[signed]_bytes
  fn to_bigint(&self) -> BigInt {
    if self.bits.is_empty() {
      Zero::zero()
    } else if self.bits[self.bits.len() - 1] {
      if self.bits.count_ones() == 1 {
        // handle min int separately
        let inc = BitVector::inc(self);
        return inc.to_bigint().checked_sub(&One::one()).unwrap();
      } else {
        // negations are fast because big int is sign-magnitude
        let neg = BitVector::neg(self);
        return neg.to_bigint().neg();
      }
    } else {
      let mut ans: BigInt = Zero::zero();
      for i in 0..self.bits.len() {
        ans.set_bit(i.try_into().unwrap(), self.bits[i])
      }
      return ans;
    }
  }

  fn to_biguint(&self) -> BigUint {
    let mut ans: BigUint = Zero::zero();
    for i in 0..self.bits.len() {
      ans.set_bit(i.try_into().unwrap(), self.bits[i])
    }
    ans
  }

  fn from_bigint(b: BigInt, width: usize) -> Self {
    let mut bits = BitVec::new();
    for i in 0..width {
      bits.push(b.bit(i.try_into().unwrap()));
    }

    BitVector { bits }
  }

  fn from_biguint(b: BigUint, width: usize) -> Self {
    let mut bits = BitVec::new();
    for i in 0..width {
      bits.push(b.bit(i.try_into().unwrap()));
    }

    BitVector { bits }
  }

  pub fn sgt(bv1: &BitVector, bv2: &BitVector) -> bool {
    bv1.to_bigint() > bv2.to_bigint()
  }

  pub fn ugt(bv1: &BitVector, bv2: &BitVector) -> bool {
    bv1.to_biguint() > bv2.to_biguint()
  }

  pub fn sgte(bv1: &BitVector, bv2: &BitVector) -> bool {
    bv1.to_bigint() >= bv2.to_bigint()
  }

  pub fn ugte(bv1: &BitVector, bv2: &BitVector) -> bool {
    bv1.to_biguint() >= bv2.to_biguint()
  }

  pub fn slt(bv1: &BitVector, bv2: &BitVector) -> bool {
    bv1.to_bigint() < bv2.to_bigint()
  }

  pub fn ult(bv1: &BitVector, bv2: &BitVector) -> bool {
    bv1.to_biguint() < bv2.to_biguint()
  }

  pub fn slte(bv1: &BitVector, bv2: &BitVector) -> bool {
    bv1.to_bigint() <= bv2.to_bigint()
  }

  pub fn ulte(bv1: &BitVector, bv2: &BitVector) -> bool {
    bv1.to_biguint() <= bv2.to_biguint()
  }

  pub fn and(bv1: &BitVector, bv2: &BitVector) -> Self {
    let mut bits = bv1.bits.clone();
    bits &= bv2.bits.as_bitslice();
    BitVector { bits }
  }

  pub fn nand(bv1: &BitVector, bv2: &BitVector) -> Self {
    let mut bits = bv1.bits.clone();
    bits &= bv2.bits.as_bitslice();
    BitVector { bits: !bits }
  }

  pub fn nor(bv1: &BitVector, bv2: &BitVector) -> Self {
    BitVector::not(&BitVector::or(bv1, bv2))
  }

  pub fn or(bv1: &BitVector, bv2: &BitVector) -> Self {
    let mut bits = bv1.bits.clone();
    bits |= bv2.bits.as_bitslice();
    BitVector { bits }
  }

  pub fn xnor(bv1: &BitVector, bv2: &BitVector) -> Self {
    BitVector::not(&BitVector::xor(bv1, bv2))
  }

  pub fn xor(bv1: &BitVector, bv2: &BitVector) -> Self {
    let mut bits = bv1.bits.clone();
    bits ^= bv2.bits.as_bitslice();
    BitVector { bits }
  }

  pub fn rol(_bv1: &BitVector, _bv2: &BitVector) -> Self {
    todo!()
  }

  pub fn ror(_bv1: &BitVector, _bv2: &BitVector) -> Self {
    todo!()
  }

  pub fn sll(_bv1: &BitVector, _bv2: &BitVector) -> Self {
    todo!()
  }

  pub fn sra(_bv1: &BitVector, _bv2: &BitVector) -> Self {
    todo!()
  }

  pub fn srl(_bv1: &BitVector, _bv2: &BitVector) -> Self {
    todo!()
  }

  pub fn add(bv1: &BitVector, bv2: &BitVector) -> Self {
    BitVector::from_biguint(bv1.to_biguint().add(bv2.to_biguint()), bv1.bits.len())
  }

  pub fn mul(bv1: &BitVector, bv2: &BitVector) -> Self {
    BitVector::from_biguint(bv1.to_biguint().mul(bv2.to_biguint()), bv1.bits.len())
  }

  pub fn sub(bv1: &BitVector, bv2: &BitVector) -> Self {
    BitVector::from_bigint(
      bv1.to_bigint().checked_sub(&bv2.to_bigint()).unwrap(),
      bv1.bits.len(),
    )
  }
}

impl From<usize> for BitVector {
  fn from(i: usize) -> Self {
    let bitvec = BitVec::from_element(i);
    BitVector { bits: bitvec }
  }
}

impl From<Vec<bool>> for BitVector {
  fn from(v: Vec<bool>) -> Self {
    let mut ans: BitVector = BitVector {
      bits: BitVec::new(),
    };
    for bit in v.iter() {
      ans.bits.push(*bit);
    }
    ans
  }
}

impl Display for BitVector {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(
      f,
      "BitVector(length: {}; bits: {})",
      self.bits.len(),
      self.bits
    )
  }
}

#[cfg(test)]
mod tests {

  use super::*;

  fn naive_test_eq(bv1: &BitVector, bv2: &BitVector) -> bool {
    for i in bv1.bits.iter_ones() {
      if !(bv2.bits[i]) {
        return false;
      }
    }
    for i in bv2.bits.iter_ones() {
      if !(bv1.bits[i]) {
        return false;
      }
    }
    bv1.bits.len() == bv2.bits.len()
  }

  #[test]
  /// checks internal representation (no actual logic)
  fn test_helpers() {
    let bv = BitVector::from(vec![true, false, true, true]);
    let bv_7 = BitVector::ones(4);
    let bv_7_2 = BitVector::from(vec![true, true, true, true]);
    assert!(bv.bits[0]);
    assert!(!bv.bits[1]);
    assert!(bv.bits[2]);
    assert!(bv.bits[3]);
    assert!(!naive_test_eq(&bv, &bv_7));
    assert!(naive_test_eq(&bv_7, &bv_7_2));
  }

  #[test]
  fn test_slices() {
    let bv_3 = BitVector::from(vec![true, true, false]);
    let bv_5 = BitVector::from(vec![true, false, true]);

    let bv_3_longer = BitVector::from(vec![true, true, false, false, false]);

    assert!(naive_test_eq(
      &BitVector::sign_extend(&bv_3, 2),
      &bv_3_longer
    ));
    assert!(naive_test_eq(
      &BitVector::zero_extend(&bv_3, 2),
      &bv_3_longer
    ));

    assert!(naive_test_eq(
      &BitVector::sign_extend(&bv_5, 2),
      &BitVector::from(vec![true, false, true, true, true])
    ));
    assert!(naive_test_eq(
      &BitVector::zero_extend(&bv_5, 3),
      &BitVector::from(vec![true, false, true, false, false, false])
    ));

    assert!(naive_test_eq(
      &BitVector::slice(&bv_5, 1, 1),
      &BitVector::from(vec![true])
    ));
    assert!(naive_test_eq(&BitVector::slice(&bv_5, 1, 3), &bv_5));
    assert!(naive_test_eq(
      &BitVector::slice(&bv_3_longer, 2, 5),
      &BitVector::from(vec![true, false, false, false])
    ));
  }

  #[test]
  fn test_unary() {
    let bv_0 = BitVector::from(vec![false, false]);
    let bv_1 = BitVector::from(vec![true, false]);
    let bv_2 = BitVector::from(vec![false, true]);
    let bv_3 = BitVector::from(vec![true, true]);

    assert!(naive_test_eq(&BitVector::inc(&bv_0), &bv_1));
    assert!(naive_test_eq(&BitVector::inc(&bv_1), &bv_2));
    assert!(naive_test_eq(&BitVector::inc(&bv_2), &bv_3));
    assert!(naive_test_eq(&BitVector::inc(&bv_3), &bv_0));

    assert!(naive_test_eq(&BitVector::dec(&bv_1), &bv_0));
    assert!(naive_test_eq(&BitVector::dec(&bv_2), &bv_1));
    assert!(naive_test_eq(&BitVector::dec(&bv_3), &bv_2));
    assert!(naive_test_eq(&BitVector::dec(&bv_0), &bv_3));

    assert!(naive_test_eq(&BitVector::not(&bv_0), &bv_3));
    assert!(naive_test_eq(&BitVector::not(&bv_1), &bv_2));

    // pairs add to 4
    assert!(naive_test_eq(&BitVector::neg(&bv_0), &bv_0));
    assert!(naive_test_eq(&BitVector::neg(&bv_1), &bv_3));
    assert!(naive_test_eq(&BitVector::neg(&bv_2), &bv_2));
    assert!(naive_test_eq(&BitVector::neg(&bv_3), &bv_1));

    assert!(BitVector::redand(&bv_3));
    assert!(!BitVector::redand(&bv_1));
    assert!(!BitVector::redand(&bv_2));
    assert!(!BitVector::redand(&bv_0));

    assert!(!BitVector::redor(&bv_0));
    assert!(BitVector::redor(&bv_1));
    assert!(BitVector::redor(&bv_2));
    assert!(BitVector::redor(&bv_3));

    assert!(!BitVector::redxor(&bv_0));
    assert!(BitVector::redxor(&bv_1));
    assert!(BitVector::redxor(&bv_2));
    assert!(!BitVector::redxor(&bv_3));

    assert!(naive_test_eq(
      &BitVector::neg(&BitVector::neg(&BitVector::neg(&BitVector::neg(&bv_3)))),
      &bv_3
    ));
    assert!(naive_test_eq(
      &BitVector::not(&BitVector::not(&BitVector::not(&BitVector::not(&bv_2)))),
      &bv_2
    ));
    assert!(naive_test_eq(
      &BitVector::inc(&BitVector::dec(&BitVector::dec(&BitVector::inc(&bv_2)))),
      &bv_2
    ));
  }

  #[test]
  fn test_unsigned_arithmetic_small() {
    let max = 128;
    let size = 7;

    let mut unsigned_numbers: Vec<BitVector> = Vec::new();
    unsigned_numbers.push(BitVector::zeros(size));
    for _i in 1..max {
      unsigned_numbers.push(BitVector::inc(unsigned_numbers.last().unwrap()));
    }

    for i in 0..max {
      for j in 0..max {
        let sum = BitVector::add(&unsigned_numbers[i], &unsigned_numbers[j]);
        let diff = BitVector::sub(&unsigned_numbers[i], &unsigned_numbers[j]);
        let prod = BitVector::mul(&unsigned_numbers[i], &unsigned_numbers[j]);

        // implementation-specific, behavior should be undefined in second case
        let sub_index = if i >= j { i - j } else { i + max - j };

        assert!(naive_test_eq(&sum, &unsigned_numbers[(i + j) % max]));
        assert!(naive_test_eq(&diff, &unsigned_numbers[sub_index % max]));
        assert!(naive_test_eq(&prod, &unsigned_numbers[(i * j) % max]));
        if i < j {
          assert!(BitVector::ult(&unsigned_numbers[i], &unsigned_numbers[j]));
        }
        if i <= j {
          assert!(BitVector::ulte(&unsigned_numbers[i], &unsigned_numbers[j]));
        }
        if i > j {
          assert!(BitVector::ugt(&unsigned_numbers[i], &unsigned_numbers[j]));
        }
        if i >= j {
          assert!(BitVector::ugte(&unsigned_numbers[i], &unsigned_numbers[j]));
        }
      }
    }
  }
}
