#[derive(Debug, Clone)]
pub struct BitVector<T> {
  // length of bit vector
  width: T,
  // length of 'bits' array
  len: T,
  /// 'bits' represents the bit vector in 32-bit chunks, first bit of 32-bit bv
  ///  in bits[0] is MSB, bit vector is 'filled' from LSB, hence spare bits (if
  ///  any) come in front of the MSB and are zeroed out.
  ///  E.g., for a bit vector of width 31, representing value 1:
  ///     bits[0] = 0 0000....1
  ///               ^ ^--- MSB
  ///               |--- spare bit
  bits: Vec<T>,
}

impl BitVector<usize> {
  // Add bvec handler functions here
}
