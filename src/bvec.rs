use std::ops::{Add, Mul, Neg};

use bitvector::BitVector as BVec;
use num_bigint::{BigInt, BigUint};
use num_traits::{CheckedSub, One, Zero};

use std::cmp::min;

#[derive(Debug, Clone)]
pub struct BitVector {
  bits: BVec,
  width: usize,
}

impl BitVector {
  pub fn zeros(len: usize) -> Self {
    let ans: BitVector = BitVector {
      bits: BVec::new(len),
      width: len,
    };
    ans
  }

  pub fn ones(len: usize) -> Self {
    BitVector {
      bits: BVec::ones(len),
      width: len,
    }
  }

  pub fn from_bits(bits: Vec<bool>) -> Self {
    let mut ans: BitVector = BitVector {
      bits: BVec::new(bits.len()),
      width: bits.len(),
    };
    for i in 0..ans.width {
      if bits[i] {
        ans.bits.insert(i);
      }
    }
    ans
  }

  pub fn from_bits_with_len(bits: Vec<bool>, w: usize) -> Self {
    let mut ans: BitVector = BitVector {
      bits: BVec::new(w),
      width: w,
    };
    for i in 0..min(w, bits.len()) {
      if bits[i] {
        ans.bits.insert(i);
      }
    }
    ans
  }

  pub fn sign_extend(bv: &BitVector, w: usize) -> Self {
    let mut other_vec: bitvector::BitVector = BVec::new(bv.width + w);
    other_vec.insert_all(&bv.bits);
    if bv.bits.contains(bv.width - 1) {
      for i in bv.width..bv.width + w {
        other_vec.insert(i);
      }
    }
    BitVector {
      bits: other_vec,
      width: bv.width + w,
    }
  }

  pub fn zero_extend(bv: &BitVector, w: usize) -> Self {
    let mut other_vec: bitvector::BitVector = BVec::new(bv.width + w);
    other_vec.insert_all(&bv.bits);
    BitVector {
      bits: other_vec,
      width: bv.width + w,
    }
  }

  pub fn slice(bv: &BitVector, l: usize, u: usize) -> Self {
    let mut other_vec: bitvector::BitVector = BVec::new(u - l + 1);
    for i in (l - 1)..u {
      if bv.bits.contains(i) {
        other_vec.insert(i - (l - 1));
      }
    }

    BitVector {
      bits: other_vec,
      width: u - l + 1,
    }
  }

  pub fn not(bv: &BitVector) -> Self {
    let mut other_vec = bitvector::BitVector::new(bv.width);
    for i in 0..bv.width {
      if !bv.bits.contains(i) {
        other_vec.insert(i);
      }
    }
    BitVector {
      bits: other_vec,
      width: bv.width,
    }
  }

  pub fn inc(bv: &BitVector) -> Self {
    let mut missing: usize = 0;
    while missing < bv.width && bv.bits.contains(missing) {
      missing += 1
    }
    if missing == bv.width {
      BitVector::zeros(bv.width)
    } else {
      let mut ans = bv.clone();
      ans.bits.insert(missing);
      for i in 0..missing {
        ans.bits.remove(i);
      }
      ans
    }
  }

  pub fn dec(bv: &BitVector) -> Self {
    let mut present: usize = 0;
    while present < bv.width && !bv.bits.contains(present) {
      present += 1
    }
    if present == bv.width {
      BitVector::ones(bv.width)
    } else {
      let mut ans = bv.clone();
      ans.bits.remove(present);
      for i in 0..present {
        ans.bits.insert(i);
      }
      ans
    }
  }

  pub fn neg(bv: &BitVector) -> Self {
    BitVector::inc(&BitVector::not(bv))
  }

  pub fn redand(bv: &BitVector) -> bool {
    bv.bits.len() == bv.width
  }

  pub fn redor(bv: &BitVector) -> bool {
    !bv.bits.is_empty()
  }

  pub fn redxor(bv: &BitVector) -> bool {
    bv.bits.len() % 2 == 1
  }

  pub fn iff(_bv1: &BitVector, _bv2: &BitVector) -> bool {
    todo!()
  }

  pub fn implies(_bv1: &BitVector, _bv2: &BitVector) -> bool {
    todo!()
  }

  pub fn eq(bv1: &BitVector, bv2: &BitVector) -> bool {
    if bv1.bits.len() != bv2.bits.len() {
      return false;
    }
    for i in &bv1.bits {
      if !(bv2.bits.contains(i)) {
        return false;
      }
    }
    true
  }

  pub fn neq(bv1: &BitVector, bv2: &BitVector) -> bool {
    if bv1.bits.len() != bv2.bits.len() {
      return true;
    }
    for i in &bv1.bits {
      if !(bv2.bits.contains(i)) {
        return false;
      }
    }
    true
  }

  // a more intelligent implementation of this would be
  //to construct the vector of bytes and pass that to from_[signed]_bytes
  fn to_bigint(&self) -> BigInt {
    if self.bits.is_empty() {
      Zero::zero()
    } else if self.bits.contains(self.width - 1) {
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
        ans.set_bit(i.try_into().unwrap(), self.bits.contains(i))
      }
      return ans;
    }
  }

  fn to_biguint(&self) -> BigUint {
    let mut ans: BigUint = Zero::zero();
    for i in 0..self.width {
      ans.set_bit(i.try_into().unwrap(), self.bits.contains(i))
    }
    ans
  }

  pub fn from_bigint(b: BigInt, width: usize) -> Self {
    let mut bits = BVec::new(width);
    for i in 0..width {
      if b.bit(i.try_into().unwrap()) {
        bits.insert(i);
      }
    }

    BitVector { width, bits }
  }

  fn from_biguint(b: BigUint, width: usize) -> Self {
    let mut bits = BVec::new(width);
    for i in 0..width {
      if b.bit(i.try_into().unwrap()) {
        bits.insert(i);
      }
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
    BitVector {
      bits: bv1.bits.intersection(&bv2.bits),
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
    BitVector {
      bits: bv1.bits.union(&bv2.bits),
      width: bv1.width,
    }
  }

  pub fn xnor(bv1: &BitVector, bv2: &BitVector) -> Self {
    BitVector::not(&BitVector::xor(bv1, bv2))
  }

  pub fn xor(bv1: &BitVector, bv2: &BitVector) -> Self {
    BitVector {
      bits: bv1
        .bits
        .difference(&bv2.bits)
        .union(&bv2.bits.difference(&bv1.bits)),
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
    for i in &bv1.bits {
      if !(bv2.bits.contains(i)) {
        return false;
      }
    }
    for i in &bv2.bits {
      if !(bv1.bits.contains(i)) {
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
    assert!(bv.bits.contains(0));
    assert!(!bv.bits.contains(1));
    assert!(bv.bits.contains(2));
    assert!(bv.bits.contains(3));
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
    let MAX = 256;
    let SIZE = 8;

    let mut unsigned_numbers: Vec<BitVector> = Vec::new();
    unsigned_numbers.push(BitVector::zeros(SIZE));
    for _i in 1..MAX {
      unsigned_numbers.push(BitVector::inc(unsigned_numbers.last().unwrap()));
    }

    for i in 0..MAX {
      for j in 0..MAX {
        let sum = BitVector::add(&unsigned_numbers[i], &unsigned_numbers[j]);
        let diff = BitVector::sub(&unsigned_numbers[i], &unsigned_numbers[j]);
        let prod = BitVector::mul(&unsigned_numbers[i], &unsigned_numbers[j]);
        let sub_index = if i >= j { i - j } else { i + MAX - j };
        assert!(naive_test_eq(&sum, &unsigned_numbers[(i + j) % MAX]));
        assert!(naive_test_eq(&diff, &unsigned_numbers[sub_index % MAX]));
        assert!(naive_test_eq(&prod, &unsigned_numbers[(i * j) % MAX]));
        if (i < j) {
          assert!(BitVector::ult(&unsigned_numbers[i], &unsigned_numbers[j]));
        }
        if (i <= j) {
          assert!(BitVector::ulte(&unsigned_numbers[i], &unsigned_numbers[j]));
        }
        if (i > j) {
          assert!(BitVector::ugt(&unsigned_numbers[i], &unsigned_numbers[j]));
        }
        if (i >= j) {
          assert!(BitVector::ugte(&unsigned_numbers[i], &unsigned_numbers[j]));
        }
      }
    }
  }

  fn test_signed_arithmetic_small() {}
}
