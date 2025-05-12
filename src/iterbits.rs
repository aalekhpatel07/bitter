/// Iterate over chunks of bits of a fixed size from a byte stream.
pub trait IterBits<'a>
where
    Self: Sized,
{
    /// Return an iterator over chunks of bits of the provided size.
    ///
    /// Example:
    ///
    /// 1. Iterate in chunks of 4 bits over a bunch of bytes.
    /// ```rust
    /// use bitter::{IterBits, Bits};
    ///
    /// // 2 bytes.
    /// let bytes = [0xff, 0xf0];
    /// let mut iter = bytes.iter().copied();
    /// let mut iter = iter.iter_bits(4);
    /// assert_eq!(iter.next(), Some(Bits::Full(0x0f)));
    /// assert_eq!(iter.next(), Some(Bits::Full(0x0f)));
    /// assert_eq!(iter.next(), Some(Bits::Full(0x0f)));
    /// assert_eq!(iter.next(), Some(Bits::Full(0x00)));
    /// assert_eq!(iter.next(), None);
    /// ```
    ///
    /// 2. Iterate in chunks of 3 bits over 2 bytes (i.e. 5 full chunks, and 1 partial chunk of 1 bit.)
    /// ```rust
    /// use bitter::{IterBits, Bits};
    ///
    /// // 2 bytes.
    /// let bytes = [0xff, 0xf0];
    /// let mut iter = bytes.iter().copied();
    /// let mut iter = iter.iter_bits(3);
    /// assert_eq!(iter.next(), Some(Bits::Full(0b111)));
    /// assert_eq!(iter.next(), Some(Bits::Full(0b111)));
    /// assert_eq!(iter.next(), Some(Bits::Full(0b111)));
    /// assert_eq!(iter.next(), Some(Bits::Full(0b111)));
    /// assert_eq!(iter.next(), Some(Bits::Full(0b000)));
    /// assert_eq!(iter.next(), Some(Bits::Partial(0x0)));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn iter_bits(&'a mut self, num_bits: usize) -> BitIterator<'a, Self>;
}

impl<'it, I> IterBits<'it> for I
where
    I: Iterator<Item = u8>,
{
    fn iter_bits(&'it mut self, num_bits: usize) -> BitIterator<'it, Self> {
        BitIterator::new(self, num_bits)
    }
}

/// An iterator that tracks chunks of bits that need to be
/// yielded from a stream of bytes.
#[derive(Debug)]
pub struct BitIterator<'a, I> {
    iter: &'a mut I,
    num_bits: usize,
    previous: Option<u8>,
    previous_trailing_bits: usize,
    current: Option<u8>,
    start_index: usize,
}

impl<'a, I> BitIterator<'a, I>
where
    I: Iterator<Item = u8>,
{
    /// Create a new BitIterator from the provided iterator
    /// of bytes, that yields chunks of bits of the provided size.
    pub fn new(iter: &'a mut I, num_bits: usize) -> Self {
        Self {
            iter,
            num_bits,
            previous: None,
            current: None,
            previous_trailing_bits: 0,
            start_index: 0,
        }
    }
}

/// Given a byte, and a position identifer, and a desired length
/// return the underlying bit slice starting at the position from the
/// left, and is of the provided size.
fn bits_at(byte: u8, start_left: usize, length: usize) -> u8 {
    let mut res: u8 = 0;
    for idx in start_left..start_left + length {
        res |= byte & (1 << (7 - idx))
    }
    res >> (8 - (start_left + length))
}

/// Represent whether a full chunk or a partial
/// chunk of bits is contained in the underlying byte
/// value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Bits {
    Full(u8),
    Partial(u8),
}

impl From<Bits> for u8 {
    fn from(value: Bits) -> Self {
        value.value()
    }
}

impl Bits {
    /// Return the underlying byte.
    pub fn value(&self) -> u8 {
        match self {
            Self::Full(value) => *value,
            Self::Partial(value) => *value,
        }
    }

    /// Return the `Some` variant if the underlying byte
    /// represents a full chunk of bits, otherwise `None`.
    pub fn as_full(&self) -> Option<u8> {
        match self {
            Self::Full(value) => Some(*value),
            _ => None,
        }
    }

    /// Return the `Some` variant if the underlying byte
    /// represents a partial chunk of bits, otherwise `None`.
    pub fn as_partial(&self) -> Option<u8> {
        match self {
            Self::Partial(value) => Some(*value),
            _ => None,
        }
    }
}

impl<I> Iterator for BitIterator<'_, I>
where
    I: Iterator<Item = u8>,
{
    type Item = Bits;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current.is_none() {
            match self.iter.next() {
                Some(byte) => {
                    self.current = Some(byte);
                }
                None => {
                    if let Some(previous) = self.previous {
                        if self.start_index == 8 {
                            return None;
                        }
                        let val = bits_at(
                            previous,
                            8 - self.previous_trailing_bits,
                            self.previous_trailing_bits,
                        );
                        self.previous = None;
                        return Some(Bits::Partial(val));
                    }
                    return None;
                }
            }
        }

        // if previous exists
        if let Some(previous) = self.previous {
            // use all previous trailing bits.
            let trailing_bits = self.previous_trailing_bits;
            let to_take_from_current: u8 = (self.num_bits - trailing_bits) as u8;
            let left = bits_at(previous, 8 - trailing_bits, trailing_bits);
            let right = bits_at(self.current.unwrap(), 0, to_take_from_current as usize);
            let joined = (left << to_take_from_current) | right;
            self.start_index = to_take_from_current as usize;
            self.previous = None;
            return Some(Bits::Full(joined));
        }

        let current = self.current.unwrap();
        if self.start_index + self.num_bits <= 8 {
            let res = bits_at(current, self.start_index, self.num_bits);
            self.start_index += self.num_bits;
            Some(Bits::Full(res))
        } else {
            let can_take = 8 - self.start_index;
            self.previous = Some(current);
            self.current = None;
            self.previous_trailing_bits = can_take;
            self.next()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bits_at() {
        let byte: u8 = 0b1010_1010;
        assert_eq!(bits_at(byte, 0, 3), 0b101);
        assert_eq!(bits_at(byte, 3, 3), 0b010);
        assert_eq!(bits_at(byte, 6, 2), 0b10);
    }
    #[test]
    fn test_bit_iterator() {
        let bytes: Vec<u8> = vec![0b10101010, 0b10101010];
        let mut iter = bytes.iter().copied();
        let mut bit_iter = iter.iter_bits(3);
        assert_eq!(bit_iter.next(), Some(Bits::Full(0b101)));
        assert_eq!(bit_iter.next(), Some(Bits::Full(0b010)));
        assert_eq!(bit_iter.next(), Some(Bits::Full(0b101)));
        assert_eq!(bit_iter.next(), Some(Bits::Full(0b010)));
        assert_eq!(bit_iter.next(), Some(Bits::Full(0b101)));
        assert_eq!(bit_iter.next(), Some(Bits::Partial(0b0)));
    }

    #[test]
    fn test_bit_iterator_all_ones_even() {
        // 80 bits
        let bytes: Vec<u8> = vec![u8::MAX; 10];
        let mut iter = bytes.iter().copied();
        let mut bit_iter = iter.iter_bits(4);
        for _ in 0..20 {
            assert_eq!(bit_iter.next(), Some(Bits::Full(0b1111)));
        }
        assert_eq!(bit_iter.next(), None);
    }

    #[test]
    fn test_bit_iterator_all_zeroes_two_trailing() {
        // 80 bits
        let bytes: Vec<u8> = vec![0b0; 10];
        let mut iter = bytes.iter().copied();
        let mut bit_iter = iter.iter_bits(7);
        for _ in 0..11 {
            assert_eq!(bit_iter.next(), Some(Bits::Full(0b0)));
        }
        assert_eq!(bit_iter.next(), Some(Bits::Partial(0b000)));
    }
}
