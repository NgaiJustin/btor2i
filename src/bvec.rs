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
    fn reserve(&mut self, n: u64) {
        let goal_length: usize = (n / 64).try_into().unwrap();

        while self.bits.len() < goal_length {
            self.bits.push(0);
        }
    }

    fn get(&self, i: u64) -> bool{
        assert! (0 <= i && i < self.width);
        let idx: usize = (i / 64).try_into().unwrap();
        self.bits[idx] & (1 << (i % 64)) != 0
    }

    fn set(&mut self, i: u64, b: bool) {
        assert! (0 <= i && i < self.width);
        let idx: usize = (i / 64).try_into().unwrap();
        if b {
            self.bits[idx] |= 1 << (i % 64);
        } else {
            self.bits[idx] &= !(1 << (i % 64));
        }
    }


    fn sign_extend(&self, w: u64) -> BitVector<u64> {
        let mut ans = self.clone();
        ans.width += w;
        ans.reserve(self.width + w);
        for i in self.width .. self.width + w - 1 {
            ans.set(i, self.get(self.width - 1));
        }
        ans
    }

    fn zero_extend(&self, w: u64) -> BitVector<u64> {
        let mut ans = self.clone();
        ans.width += w;
        ans.reserve(self.width + w);
        for i in self.width .. self.width + w - 1 {
            ans.set(i, false);
        }
        ans
    }

    fn slice(&self, u: u64, l: u64) -> BitVector<u64> {
        let mut ans = self.clone();
        ans.width = u - l + 1;
        for i in (l - 1) .. u {
            ans.set(i - (l - 1), self.get(i));
        }
        ans
    }
}
