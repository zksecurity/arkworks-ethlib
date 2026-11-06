//! Installation smoke test, not the arkworks serializer.
pub fn set_compression_flag(byte: u8) -> u8 {
    byte | 0x80
}
