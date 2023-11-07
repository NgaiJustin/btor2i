use std::ops::Add;

#[derive(Debug, Clone)]
pub struct BitVector<T> {
  // length of bit vector
  width: T,
  /// 'bits' represents the bit vector in chunks, first bit of integer
  ///  in bits[0] is LSB, bit vector is 'filled' from LSB, hence spare bits (if
  ///  any) come in front of the MSB and are zeroed out.
  ///  E.g., for a bit vector of width 31, representing value 1:
  ///     bits[0] = 0 0000....1
  ///               ^ ^--- MSB
  ///               |--- spare bit
  bits: Vec<T>,
}

impl BitVector<u64> {
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
      for j in (0 as u64)..7 {
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

  fn from_bytes(bytes: Vec<u8>, width: u64, signed: bool) -> BitVector<u64> {
    let mut ans: BitVector<u64> = BitVector {
      width: width,
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

  fn sign_extend(&self, w: u64) -> BitVector<u64> {
    let mut ans = self.clone();
    ans.width += w;
    ans.reserve(self.width + w);
    for i in self.width..self.width + w - 1 {
      ans.set(i, self.get(self.width - 1));
    }
    ans
  }

  fn zero_extend(&self, w: u64) -> BitVector<u64> {
    let mut ans = self.clone();
    ans.width += w;
    ans.reserve(self.width + w);
    for i in self.width..self.width + w - 1 {
      ans.set(i, false);
    }
    ans
  }

  fn slice(&self, u: u64, l: u64) -> BitVector<u64> {
    let mut ans = self.clone();
    ans.width = u - l + 1;
    for i in (l - 1)..u {
      ans.set(i - (l - 1), self.get(i));
    }
    ans
  }

  fn not(&self) -> BitVector<u64> {
    let mut ans = self.clone();
    for i in 1..(self.width - 1) {
      ans.set(i, !ans.get(i));
    }
    ans
  }

  fn inc(&self) -> BitVector<u64> {
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

  fn add(left: BitVector<u64>, right: BitVector<u64>) -> BitVector<u64> {
    let left_bytes: Vec<u8> = left.to_bytes(true);
    let right_bytes: Vec<u8> = right.to_bytes(true);
    let ans: Vec<u8> = num_bigint::BigInt::from_signed_bytes_le(left_bytes.as_ref())
      .add(num_bigint::BigInt::from_signed_bytes_le(
        right_bytes.as_ref(),
      ))
      .to_signed_bytes_le();
    return BitVector::<u64>::from_bytes(ans, left.width, true);
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_get() {
    let mut bv = BitVector::<u64> {
      width: 64,
      bits: vec![0, 0],
    };
    bv.set(0, true);
    assert_eq!(bv.get(0), true);
    assert_eq!(bv.get(1), false);
    bv.set(1, true);
    assert_eq!(bv.get(0), true);
    assert_eq!(bv.get(1), true);
  }

  #[test]
  fn test_set() {
    let mut bv = BitVector::<u64> {
      width: 64,
      bits: vec![0, 0],
    };
    bv.set(0, true);
    assert_eq!(bv.get(0), true);
    assert_eq!(bv.get(1), false);
    bv.set(1, true);
    assert_eq!(bv.get(0), true);
    assert_eq!(bv.get(1), true);
  }

  #[test]
  fn test_to_bytes() {
    let mut bv = BitVector::<u64> {
      width: 64,
      bits: vec![0, 0],
    };
    // set all bits to 1
    for i in 0..64 {
      bv.set(i, true);
    }
    let bytes = bv.to_bytes(false);
    assert_eq!(bytes.len(), 8);

    // check that all bytes are 255
    for i in 0..7 {
      assert_eq!(bytes[i], 255);
    }
  }
}
