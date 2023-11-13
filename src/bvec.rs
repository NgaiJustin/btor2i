extern crate bitvector;
use std::ops::{Neg, Add, Mul};

use bitvector::BitVector as BVec;
use num_bigint::{BigInt, BigUint};
use num_traits::{Zero, CheckedAdd, CheckedSub, CheckedMul, CheckedDiv, CheckedRem};


#[derive(Debug, Clone)]
pub struct BitVectorNew {
  bits: BVec,
  width: usize,
}

impl BitVectorNew {
  pub fn zeros(len: usize) -> Self {
    let ans: BitVectorNew = BitVectorNew {
      bits: BVec::new(len),
      width: len,
    };
    ans
  }

  pub fn ones(len: usize) -> Self {
    BitVectorNew {
      bits: BVec::ones(len),
      width: len,
    }
  }

  pub fn from_bits(bits: Vec<bool>) -> Self {
    let mut ans: BitVectorNew = BitVectorNew {
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

  pub fn sign_extend(bv: &BitVectorNew, w: usize) -> Self {
    let mut other_vec: bitvector::BitVector = BVec::new(bv.width + w);
    other_vec.insert_all(&bv.bits);
    if bv.bits.contains(bv.width - 1) {
      for i in bv.width..bv.width + w {
        other_vec.insert(i);
      }
    }
    BitVectorNew {
      bits: other_vec,
      width: bv.width + w,
    }
  }

  pub fn zero_extend(bv: &BitVectorNew, w: usize) -> Self {
    let mut other_vec: bitvector::BitVector = BVec::new(bv.width + w);
    other_vec.insert_all(&bv.bits);
    BitVectorNew {
      bits: other_vec,
      width: bv.width + w,
    }
  }

  pub fn slice(bv: &BitVectorNew, l: usize, u: usize) -> Self {
    let mut other_vec: bitvector::BitVector = BVec::new(u - l + 1);
    for i in (l - 1)..u {
      if bv.bits.contains(i) {
        other_vec.insert(i - (l - 1));
      }
    }

    BitVectorNew {
      bits: other_vec,
      width: u - l + 1,
    }
  }

  pub fn not(bv: &BitVectorNew) -> Self {
    let mut other_vec = bitvector::BitVector::new(bv.width);
    for i in 0..bv.width {
      if !bv.bits.contains(i) {
        other_vec.insert(i);
      }
    }
    BitVectorNew {
      bits: other_vec,
      width: bv.width,
    }
  }

  pub fn inc(bv: &BitVectorNew) -> Self {
    let mut missing: usize = 0;
    while missing < bv.width && bv.bits.contains(missing) {
      missing += 1
    }
    if missing == bv.width {
      BitVectorNew::zeros(bv.width)
    } else {
      let mut ans = bv.clone();
      ans.bits.insert(missing);
      for i in 0..missing {
        ans.bits.remove(i);
      }
      ans
    }
  }

  pub fn dec(bv: &BitVectorNew) -> Self {
    let mut present: usize = 0;
    while present < bv.width && !bv.bits.contains(present) {
      present += 1
    }
    if present == bv.width {
      BitVectorNew::ones(bv.width)
    } else {
      let mut ans = bv.clone();
      ans.bits.remove(present);
      for i in 0..present {
        ans.bits.insert(i);
      }
      ans
    }
  }

  pub fn neg(bv: &BitVectorNew) -> Self {
    BitVectorNew::inc(&BitVectorNew::not(bv))
  }

  pub fn redand(bv: &BitVectorNew) -> bool {
    bv.bits.len() == bv.width
  }

  pub fn redor(bv: &BitVectorNew) -> bool {
    !bv.bits.is_empty()
  }

  pub fn redxor(bv: &BitVectorNew) -> bool {
    bv.bits.len() % 2 == 1
  }

  pub fn iff(bv1: &BitVectorNew, bv2: &BitVectorNew) -> bool {
    todo!()
  }

  pub fn implies(bv1: &BitVectorNew, bv2: &BitVectorNew) -> bool {
    todo!()
  }

  pub fn eq(bv1: &BitVectorNew, bv2: &BitVectorNew) -> bool {
    if (bv1.bits.len() != bv2.bits.len()) {
        return false;
    }
    for i in &bv1.bits {
        if !(bv2.bits.contains(i)) {
            return false
        }
    }
    return true;
  }

  pub fn neq(bv1: &BitVectorNew, bv2: &BitVectorNew) -> bool {
    if (bv1.bits.len() != bv2.bits.len()) {
        return true;
    }
    for i in &bv1.bits {
        if !(bv2.bits.contains(i)) {
            return false
        }
    }
    return true
    
  }

  // a more intelligent implementation of this would be
  //to construct the vector of bytes and pass that to from_[signed]_bytes
  fn to_bigint(&self) -> BigInt {
    if (self.bits.len() == 0) {
        return Zero::zero();

    } else if (self.bits.contains (self.width - 1)) {
        let neg = BitVectorNew::neg(self);
        return neg.to_bigint().neg();
    }
    else {
        let mut ans: BigInt = Zero::zero();
        for i in (0 .. self.width) {
            ans.set_bit(i.try_into().unwrap(), self.bits.contains(i))
        }
        return ans;
    }
}

  fn to_biguint(&self) -> BigUint {
    let mut ans: BigUint = Zero::zero();
    for i in (0 .. self.width) {
        ans.set_bit(i.try_into().unwrap(), self.bits.contains(i))
    }
    return ans;
  }

  fn from_bigint(b: BigInt, width: usize) -> Self {
    let mut bits = BVec::new(width);
    for i in (0 .. width) {
        if (b.bit(i.try_into().unwrap())) {
            bits.insert(i);
        }
    }

    BitVectorNew {
        width: width,
        bits: bits
    }
  }

  fn from_biguint(b: BigUint, width: usize) -> Self {
    let mut bits = BVec::new(width);
    for i in (0 .. width) {
        if (b.bit(i.try_into().unwrap())) {
            bits.insert(i);
        }
    }

    BitVectorNew {
        width: width,
        bits: bits
    }
  }

  pub fn sgt(bv1: &BitVectorNew, bv2: &BitVectorNew) -> bool {
    bv1.to_bigint() > bv2.to_bigint()
  }

  pub fn ugt(bv1: &BitVectorNew, bv2: &BitVectorNew) -> bool {
    bv1.to_biguint() > bv2.to_biguint()
  }

  pub fn sgte(bv1: &BitVectorNew, bv2: &BitVectorNew) -> bool {
    bv1.to_bigint() >= bv2.to_bigint()
  }

  pub fn ugte(bv1: &BitVectorNew, bv2: &BitVectorNew) -> bool {
    bv1.to_biguint() >= bv2.to_biguint()
  }

  pub fn slt(bv1: &BitVectorNew, bv2: &BitVectorNew) -> bool {
    bv1.to_bigint() < bv2.to_bigint()
  }

  pub fn ult(bv1: &BitVectorNew, bv2: &BitVectorNew) -> bool {
    bv1.to_biguint() < bv2.to_biguint()
  }

  pub fn slte(bv1: &BitVectorNew, bv2: &BitVectorNew) -> bool {
    bv1.to_bigint() <= bv2.to_bigint()
  }

  pub fn ulte(bv1: &BitVectorNew, bv2: &BitVectorNew) -> bool {
    bv1.to_biguint() <= bv2.to_biguint()
  }


  /// these are also kinda inefficient
  pub fn and(bv1: &BitVectorNew, bv2: &BitVectorNew) -> Self {
    BitVectorNew { bits: bv1.bits.intersection(&bv2.bits), width: bv1.width }
  }

  pub fn nand(bv1: &BitVectorNew, bv2: &BitVectorNew) -> Self {
    BitVectorNew::not(&BitVectorNew::and(&bv1, &bv2))
  }

  pub fn nor(bv1: &BitVectorNew, bv2: &BitVectorNew) -> Self {
    BitVectorNew::not(&BitVectorNew::or(&bv1, &bv2))
  }

  pub fn or(bv1: &BitVectorNew, bv2: &BitVectorNew) -> Self {
    BitVectorNew { bits: bv1.bits.union(&bv2.bits), width: bv1.width }
  }

  pub fn xnor(bv1: &BitVectorNew, bv2: &BitVectorNew) -> Self {
    BitVectorNew::not(&BitVectorNew::xor(&bv1, &bv2))
  }

  pub fn xor(bv1: &BitVectorNew, bv2: &BitVectorNew) -> Self {
    BitVectorNew { bits: bv1.bits.difference(&bv2.bits).union(&bv2.bits.difference(&bv1.bits)), width: bv1.width }
  }

  pub fn rol(bv1: &BitVectorNew, bv2: &BitVectorNew) -> Self {
    todo!()
  }

  pub fn ror(bv1: &BitVectorNew, bv2: &BitVectorNew) -> Self {
    todo!()
  }

  pub fn sll(bv1: &BitVectorNew, bv2: &BitVectorNew) -> Self {
    todo!()
  }

  pub fn sra(bv1: &BitVectorNew, bv2: &BitVectorNew) -> Self {
    todo!()
  }

  pub fn srl(bv1: &BitVectorNew, bv2: &BitVectorNew) -> Self {
    todo!()
  }

  pub fn add(bv1: &BitVectorNew, bv2: &BitVectorNew) -> Self {
    BitVectorNew::from_biguint(bv1.to_biguint().add(bv2.to_biguint()), bv1.width)
  }

  pub fn mul(bv1: &BitVectorNew, bv2: &BitVectorNew) -> Self {
    BitVectorNew::from_biguint(bv1.to_biguint().mul(bv2.to_biguint()), bv1.width)
  }

  pub fn sub(bv1: &BitVectorNew, bv2: &BitVectorNew) -> Self {
    BitVectorNew::from_biguint(
        bv1.to_biguint().checked_sub(&bv2.to_biguint()).unwrap(), bv1.width)
  }

}

#[cfg(test)]
mod tests {
  use super::*;

  fn naive_test_eq(bv1: &BitVectorNew, bv2: &BitVectorNew) -> bool {
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
    let bv = BitVectorNew::from_bits( vec![true, false, true, true] );
    let bv_7 = BitVectorNew::ones(4);
    let bv_7_2 = BitVectorNew::from_bits(vec![true, true, true, true]);
    assert! (bv.bits.contains(0));
    assert! (!bv.bits.contains(1));
    assert! (bv.bits.contains(2));
    assert! (bv.bits.contains(3));
    assert! (!naive_test_eq(&bv, &bv_7));
    assert! (naive_test_eq(&bv_7, &bv_7_2));
  }

  #[test]
  fn test_slices() {
    let bv_3 = BitVectorNew::from_bits(vec![true, true, false]);
    let bv_5 = BitVectorNew::from_bits(vec![true, false, true]);
    
    let bv_3_longer = BitVectorNew::from_bits(vec![true, true, false, false, false]);

    assert! (naive_test_eq(&BitVectorNew::sign_extend(&bv_3, 2), &bv_3_longer));
    assert! (naive_test_eq(&BitVectorNew::zero_extend(&bv_3, 2), &bv_3_longer));

    assert! (naive_test_eq(&BitVectorNew::sign_extend(&bv_5, 2), &BitVectorNew::from_bits(vec![true, false, true, true, true])));
    assert! (naive_test_eq(&BitVectorNew::zero_extend(&bv_5, 3), &BitVectorNew::from_bits(vec![true, false, true, false, false, false])));

    assert! (naive_test_eq(&BitVectorNew::slice(&bv_5, 1, 1), &BitVectorNew::from_bits(vec![true])));
    assert! (naive_test_eq(&BitVectorNew::slice(&bv_5, 1, 3), &bv_5));
    assert! (naive_test_eq(&BitVectorNew::slice(&bv_3_longer, 2, 5), &BitVectorNew::from_bits(vec![true, false, false, false])));
  }

  #[test]
  fn test_unary() {
    let bv_0 = BitVectorNew::from_bits(vec![false, false]);
    let bv_1 = BitVectorNew::from_bits(vec![true, false]);
    let bv_2 = BitVectorNew::from_bits(vec![false, true]);
    let bv_3 = BitVectorNew::from_bits(vec![true, true]);

    assert! (naive_test_eq(&BitVectorNew::inc(&bv_0), &bv_1));
    assert! (naive_test_eq(&BitVectorNew::inc(&bv_1), &bv_2));
    assert! (naive_test_eq(&BitVectorNew::inc(&bv_2), &bv_3));
    assert! (naive_test_eq(&BitVectorNew::inc(&bv_3), &bv_0));
    
    assert! (naive_test_eq(&BitVectorNew::dec(&bv_1), &bv_0));
    assert! (naive_test_eq(&BitVectorNew::dec(&bv_2), &bv_1));
    assert! (naive_test_eq(&BitVectorNew::dec(&bv_3), &bv_2));
    assert! (naive_test_eq(&BitVectorNew::dec(&bv_0), &bv_3));

    assert! (naive_test_eq(&BitVectorNew::not(&bv_0), &bv_3));
    assert! (naive_test_eq(&BitVectorNew::not(&bv_1), &bv_2));


    // pairs add to 4
    assert! (naive_test_eq(&BitVectorNew::neg(&bv_0), &bv_0));
    assert! (naive_test_eq(&BitVectorNew::neg(&bv_1), &bv_3));
    assert! (naive_test_eq(&BitVectorNew::neg(&bv_2), &bv_2));
    assert! (naive_test_eq(&BitVectorNew::neg(&bv_3), &bv_1));

    assert! (BitVectorNew::redand(&bv_3));
    assert! (!BitVectorNew::redand(&bv_1));
    assert! (!BitVectorNew::redand(&bv_2));
    assert! (!BitVectorNew::redand(&bv_0));
    
    assert! (!BitVectorNew::redor(&bv_0));
    assert! (BitVectorNew::redor(&bv_1));
    assert! (BitVectorNew::redor(&bv_2));
    assert! (BitVectorNew::redor(&bv_3));

    assert! (!BitVectorNew::redxor(&bv_0));
    assert! (BitVectorNew::redxor(&bv_1));
    assert! (BitVectorNew::redxor(&bv_2));
    assert! (!BitVectorNew::redxor(&bv_3));

    assert! (naive_test_eq(&BitVectorNew::neg(&BitVectorNew::neg(&BitVectorNew::neg(&BitVectorNew::neg(&bv_3)))), &bv_3));
    assert! (naive_test_eq(&BitVectorNew::not(&BitVectorNew::not(&BitVectorNew::not(&BitVectorNew::not(&bv_2)))), &bv_2));
    assert! (naive_test_eq(&BitVectorNew::inc(&BitVectorNew::dec(&BitVectorNew::dec(&BitVectorNew::inc(&bv_2)))), &bv_2));
  }

  #[test]
  fn test_arithmetic() {

  }

}
