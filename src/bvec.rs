use std::ops::Add;

extern crate bitvector;
use bitvector::BitVector as BVec;

#[derive(Debug, Clone)]
pub struct BitVectorOld<T> {
  /// 'bits' represents the bit vector in chunks, first bit of integer
  ///  in bits[0] is LSB, bit vector is 'filled' from LSB, hence spare bits (if
  ///  any) come in front of the MSB and are zeroed out.
  ///  E.g., for a bit vector of width 31, representing value 1:
  ///     bits[0] = 0 0000....1
  ///               ^ ^--- MSB
  ///               |--- spare bit
  bits: Vec<T>,
  width: u64,
}

impl BitVectorOld<u64> {
  /// helper function to be used when changing width to [n]
  fn reserve(&mut self, n: u64) {
    // if n is not a multiple of 64, we need to add an extra block
    let mut goal_length: usize = (n / 64).try_into().unwrap();
    if n % 64 != 0 {
      goal_length += 1;
    }

    while self.bits.len() < goal_length {
      self.bits.push(0);
    }
  }

  fn get(&self, i: u64) -> bool {
    assert!(i < self.width);
    let idx: usize = (i / 64).try_into().unwrap();

    self.bits[idx] & (1 << (i % 64)) != 0
  }

  fn set(&mut self, i: u64, b: bool) {
    assert!(i < self.width);
    let idx: usize = (i / 64).try_into().unwrap();

    if b ^ self.get(i) {
      self.bits[idx] ^= 1 << (i % 64);
    }
  }

  fn to_bytes(&self, signed: bool) -> Vec<u8> {
    let mut bytes: Vec<u8> = Vec::new();

    // handle all but the last block
    for i in 0..(self.width / 64 - 1).try_into().unwrap() {
      for j in 0_u64..7 {
        let mask: u64 = (u64::MAX >> (8 * j)) << (8 * j);
        bytes.push(((self.bits[i] & mask) >> (8 * j)).try_into().unwrap());
      }
    }

    // handle the last block, except for the last byte
    let i: usize = (self.width / 64).try_into().unwrap();
    for j in 0..(self.width % 8 - 1).try_into().unwrap() {
      let mask: u64 = (u64::MAX >> (8 * j)) << (8 * j);
      let byte = (self.bits[i] & mask) >> (8 * j);
      bytes.push(byte.try_into().unwrap());
    }

    // handle the last byte
    let j: usize = (self.width % 8 - 1).try_into().unwrap();
    let mask: u64 = (u64::MAX >> (8 * j)) << (8 * j);
    let mut last_byte = (self.bits[i] & mask) >> (8 * j);

    if signed {
      for k in self.width % 8..8 {
        last_byte |= 1 << k;
      }
    }
    bytes.push(last_byte.try_into().unwrap());

    bytes
  }

  fn from_bytes(bytes: Vec<u8>, width: u64, signed: bool) -> BitVectorOld<u64> {
    let mut ans: BitVectorOld<u64> = BitVectorOld {
      width,
      bits: Vec::new(),
    };
    ans.reserve(width);
    for i in 0..width {
      let idx: usize = (i / 8).try_into().unwrap();
      if idx < bytes.len() {
        ans.set(i, bytes[idx] & (1 << (i % 8)) != 0);
      } else if i > 0 && signed {
        ans.set(i, ans.get(i - 1));
      } else {
        ans.set(i, false);
      }
    }
    ans
  }

  fn sign_extend(&self, w: u64) -> BitVectorOld<u64> {
    let mut ans = self.clone();
    ans.width += w;
    ans.reserve(self.width + w);
    for i in self.width..self.width + w - 1 {
      ans.set(i, self.get(self.width - 1));
    }
    ans
  }

  fn zero_extend(&self, w: u64) -> BitVectorOld<u64> {
    let mut ans = self.clone();
    ans.width += w;
    ans.reserve(self.width + w);
    for i in self.width..self.width + w - 1 {
      ans.set(i, false);
    }
    ans
  }

  fn slice(&self, u: u64, l: u64) -> BitVectorOld<u64> {
    let mut ans = self.clone();
    ans.width = u - l + 1;
    for i in (l - 1)..u {
      ans.set(i - (l - 1), self.get(i));
    }
    ans
  }

  fn not(&self) -> BitVectorOld<u64> {
    let mut ans = self.clone();
    for i in 1..(self.width - 1) {
      ans.set(i, !ans.get(i));
    }
    ans
  }

  fn inc(&self) -> BitVectorOld<u64> {
    let mut ans = self.clone();
    let i: usize = 0;
    let mut done = false;

    let last_idx = (self.width / 64 - 1).try_into().unwrap();

    // set all blocks to 0 which are 1 below their max.
    // Rust overflow is UB so have to check for overflow first.
    // if a block won't overflow, increment it and finish.
    while i < last_idx && !done {
      if ans.bits[i] == u64::MAX - 1 {
        ans.bits[i] = 0;
      } else {
        ans.bits[i] += 1;
        done = true;
      }
    }

    // try to increment last block. if it would fail, zero it instead.
    if !done {
      let last_size = self.width - (self.width / 64 - 1) * 64; // number of bits in last block, could be 64
      let mut max_val: u64 = 0;
      for i in 0..(last_size - 1) {
        max_val |= 1 << i;
      }
      if ans.bits[last_idx] == max_val {
        ans.bits[last_idx] = 0;
      } else {
        ans.bits[last_idx] += 1;
      }
    }
    ans
  }

  fn dec(&self) {}

  fn redand(&self) {}

  fn redor(&self) {}

  fn redxor(&self) {}

  fn add(left: BitVectorOld<u64>, right: BitVectorOld<u64>) -> BitVectorOld<u64> {
    let left_bytes: Vec<u8> = left.to_bytes(true);
    let right_bytes: Vec<u8> = right.to_bytes(true);
    let ans: Vec<u8> = num_bigint::BigInt::from_signed_bytes_le(left_bytes.as_ref())
      .add(num_bigint::BigInt::from_signed_bytes_le(
        right_bytes.as_ref(),
      ))
      .to_signed_bytes_le();
    BitVectorOld::<u64>::from_bytes(ans, left.width, true)
  }
}

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

  pub fn eq(_bv1: &BitVectorNew, _bv2: &BitVectorNew) -> bool {
    todo!()
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

}
