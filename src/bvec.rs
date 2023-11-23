use std::ops::{Add, Mul, Neg};

use bitvec::prelude::*;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

#[derive(Debug, Clone)]
pub struct BitVector {
  //   bits: BVec,
  bits: BitVec<usize, Lsb0>,
  width: usize,
}

impl From<usize> for BitVector {
  fn from(i: usize) -> Self {
    let bitvec = BitVec::from_element(i);
    BitVector {
      width: bitvec.len(),
      bits: bitvec,
    }
  }
}

impl BitVector {
  pub fn zeros(len: usize) -> Self {
    let mut bits = BitVec::new();
    for _ in 0..len {
      bits.push(false);
    }
    let ans: BitVector = BitVector { bits, width: len };
    ans
  }

  pub fn ones(len: usize) -> Self {
    let mut bits = BitVec::new();
    for _ in 0..len {
      bits.push(true);
    }
    BitVector { bits, width: len }
  }

  pub fn from_bits(bits: Vec<bool>) -> Self {
    let mut ans: BitVector = BitVector {
      bits: BitVec::new(),
      width: bits.len(),
    };
    for bit in bits.iter() {
      ans.bits.push(*bit);
    }
    ans
  }

  pub fn sign_extend(bv: &BitVector, w: usize) -> Self {
    let mut other_vec = BitVec::new();
    for bit in bv.bits.iter() {
      other_vec.push(*bit);
    }
    for _ in bv.width..bv.width + w {
      other_vec.push(*bv.bits.last().as_deref().unwrap());
    }
    BitVector {
      bits: other_vec,
      width: bv.width + w,
    }
  }

  pub fn zero_extend(bv: &BitVector, w: usize) -> Self {
    let mut other_vec = BitVec::new();
    for bit in bv.bits.iter() {
      other_vec.push(*bit);
    }
    BitVector {
      bits: other_vec,
      width: bv.width + w,
    }
  }

  pub fn slice(bv: &BitVector, l: usize, u: usize) -> Self {
    let mut other_vec = BitVec::new();
    for i in (l - 1)..u {
      other_vec.push(bv.bits[i]);
    }

    BitVector {
      bits: other_vec,
      width: u - l + 1,
    }
  }

  pub fn not(bv: &BitVector) -> Self {
    let bits = bv.bits.clone();
    BitVector {
      bits: !bits,
      width: bv.width,
    }
  }

  pub fn inc(bv: &BitVector) -> Self {
    let mut missing: usize = 0;
    while missing < bv.width && bv.bits[missing] {
      missing += 1
    }
    if missing == bv.width {
      BitVector::zeros(bv.width)
    } else {
      let mut ans = bv.clone();
      ans.bits.set(missing, true);
      for i in 0..missing {
        ans.bits.set(i, false);
      }
      ans
    }
  }

  pub fn dec(bv: &BitVector) -> Self {
    let mut present: usize = 0;
    while present < bv.width && !bv.bits[present] {
      present += 1
    }
    if present == bv.width {
      BitVector::ones(bv.width)
    } else {
      let mut ans = bv.clone();
      ans.bits.set(present, false);
      for i in 0..present {
        ans.bits.set(i, true);
      }
      ans
    }
  }

  pub fn neg(bv: &BitVector) -> Self {
    BitVector::inc(&BitVector::not(bv))
  }

  pub fn redand(bv: &BitVector) -> bool {
    bv.bits.count_ones() == bv.width
  }

  pub fn redor(bv: &BitVector) -> bool {
    bv.bits.count_ones() != 0
  }

  pub fn redxor(bv: &BitVector) -> bool {
    bv.bits.count_ones() % 2 == 1
  }

  pub fn iff(_bv1: &BitVector, _bv2: &BitVector) -> bool {
    todo!()
  }

  pub fn implies(_bv1: &BitVector, _bv2: &BitVector) -> bool {
    todo!()
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
    true
  }

  pub fn neq(bv1: &BitVector, bv2: &BitVector) -> bool {
    if bv1.bits.count_ones() != bv2.bits.count_ones() {
      return true;
    }
    for i in bv1.bits.iter_ones() {
      if !(bv2.bits[i]) {
        return false;
      }
    }
    true
  }

  pub fn to_usize(&self) -> usize {
    let mut ans: usize = 0;
    for i in 0..self.bits.len() {
      if self.bits[i] {
        ans += 1 << i;
      }
    }
    ans
  }

  // a more intelligent implementation of this would be
  //to construct the vector of bytes and pass that to from_[signed]_bytes
  fn to_bigint(&self) -> BigInt {
    if self.bits.is_empty() {
      Zero::zero()
    } else if self.bits[self.width - 1] {
      if self.bits.len() == 1 {
        // handle min int separately
        let inc = BitVector::inc(self);
        return inc.to_bigint().checked_sub(&One::one()).unwrap();
      } else {
        let neg = BitVector::neg(self);
        return neg.to_bigint().neg();
      }
    } else {
      let mut ans: BigInt = Zero::zero();
      for i in 0..self.width {
        ans.set_bit(i.try_into().unwrap(), self.bits[i])
      }
      return ans;
    }
  }

  fn to_biguint(&self) -> BigUint {
    let mut ans: BigUint = Zero::zero();
    for i in 0..self.width {
      ans.set_bit(i.try_into().unwrap(), self.bits[i])
    }
    ans
  }

  fn from_bigint(b: BigInt, width: usize) -> Self {
    let mut bits = BitVec::new();
    for i in 0..width {
      bits.push(b.bit(i.try_into().unwrap()));
    }

    BitVector { width, bits }
  }

  fn from_biguint(b: BigUint, width: usize) -> Self {
    let mut bits = BitVec::new();
    for i in 0..width {
      bits.push(b.bit(i.try_into().unwrap()));
    }

    BitVector { width, bits }
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

  /// these are also kinda inefficient
  pub fn and(bv1: &BitVector, bv2: &BitVector) -> Self {
    let mut bits = bv1.bits.clone();
    bits &= bv2.bits.clone();
    BitVector {
      bits,
      width: bv1.width,
    }
  }

  pub fn nand(bv1: &BitVector, bv2: &BitVector) -> Self {
    BitVector::not(&BitVector::and(bv1, bv2))
  }

  pub fn nor(bv1: &BitVector, bv2: &BitVector) -> Self {
    BitVector::not(&BitVector::or(bv1, bv2))
  }

  pub fn or(bv1: &BitVector, bv2: &BitVector) -> Self {
    let mut bits = bv1.bits.clone();
    bits |= bv2.bits.clone();
    BitVector {
      bits,
      width: bv1.width,
    }
  }

  pub fn xnor(bv1: &BitVector, bv2: &BitVector) -> Self {
    BitVector::not(&BitVector::xor(bv1, bv2))
  }

  pub fn xor(bv1: &BitVector, bv2: &BitVector) -> Self {
    let mut bits = bv1.bits.clone();
    bits ^= bv2.bits.clone();
    BitVector {
      bits,
      width: bv1.width,
    }
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
    BitVector::from_biguint(bv1.to_biguint().add(bv2.to_biguint()), bv1.width)
  }

  pub fn mul(bv1: &BitVector, bv2: &BitVector) -> Self {
    BitVector::from_biguint(bv1.to_biguint().mul(bv2.to_biguint()), bv1.width)
  }

  pub fn sub(bv1: &BitVector, bv2: &BitVector) -> Self {
    BitVector::from_bigint(
      bv1.to_bigint().checked_sub(&bv2.to_bigint()).unwrap(),
      bv1.width,
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
    bv1.width == bv2.width
  }

  #[test]
  /// checks internal representation (no actual logic)
  fn test_helpers() {
    let bv = BitVector::from_bits(vec![true, false, true, true]);
    let bv_7 = BitVector::ones(4);
    let bv_7_2 = BitVector::from_bits(vec![true, true, true, true]);
    println!("{}", bv_7.bits);
    assert!(bv.bits[0]);
    assert!(!bv.bits[1]);
    assert!(bv.bits[2]);
    assert!(bv.bits[3]);
    assert!(!naive_test_eq(&bv, &bv_7));
    assert!(naive_test_eq(&bv_7, &bv_7_2));
  }

  #[test]
  fn test_slices() {
    let bv_3 = BitVector::from_bits(vec![true, true, false]);
    let bv_5 = BitVector::from_bits(vec![true, false, true]);

    let bv_3_longer = BitVector::from_bits(vec![true, true, false, false, false]);

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
      &BitVector::from_bits(vec![true, false, true, true, true])
    ));
    assert!(naive_test_eq(
      &BitVector::zero_extend(&bv_5, 3),
      &BitVector::from_bits(vec![true, false, true, false, false, false])
    ));

    assert!(naive_test_eq(
      &BitVector::slice(&bv_5, 1, 1),
      &BitVector::from_bits(vec![true])
    ));
    assert!(naive_test_eq(&BitVector::slice(&bv_5, 1, 3), &bv_5));
    assert!(naive_test_eq(
      &BitVector::slice(&bv_3_longer, 2, 5),
      &BitVector::from_bits(vec![true, false, false, false])
    ));
  }

  #[test]
  fn test_unary() {
    let bv_0 = BitVector::from_bits(vec![false, false]);
    let bv_1 = BitVector::from_bits(vec![true, false]);
    let bv_2 = BitVector::from_bits(vec![false, true]);
    let bv_3 = BitVector::from_bits(vec![true, true]);

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
    let max = 256;
    let size = 8;

    let mut unsigned_numbers: Vec<BitVector> = Vec::new();
    unsigned_numbers.push(BitVector::zeros(size));
    for _i in 1..max {
      unsigned_numbers.push(BitVector::inc(unsigned_numbers.last().unwrap()));
    }

    for i in 0..max {
      for j in 0..max {
        let sum = BitVector::add(&unsigned_numbers[i], &unsigned_numbers[j]);
        // let diff = BitVector::sub(&unsigned_numbers[i], &unsigned_numbers[j]);
        let prod = BitVector::mul(&unsigned_numbers[i], &unsigned_numbers[j]);
        // let sub_index = if i >= j { i - j } else { i + max - j };
        assert!(naive_test_eq(&sum, &unsigned_numbers[(i + j) % max]));
        // assert!(naive_test_eq(&diff, &unsigned_numbers[sub_index % max]));
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
