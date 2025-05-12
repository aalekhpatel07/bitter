//! This crate provides an iterator, and a trait that lets a 
//! type adapt into an iterator over arbitrarily sized chunks 
//! of bits from a stream of bytes.
//! 
//! See [IterBits], [BitIterator], and [Bits].

mod iterbits;
pub use iterbits::{BitIterator, Bits, IterBits};
