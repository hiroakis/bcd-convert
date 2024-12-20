use std::convert::TryFrom;
use std::fmt;
use std::str::FromStr;
use thiserror::Error;

/// An error type indicating issues that occur during BCD parsing or conversion.
#[derive(Debug, Error, PartialEq)]
pub enum BcdError {
    /// Indicates that a nibble (4-bit segment) of the provided BCD byte
    /// is invalid (greater than 9).
    #[error("invalid BCD nibble: {0:#X}")]
    InvalidBcdNibble(u8),

    /// Indicates that the input string contains non-digit characters.
    #[error("input string contains non-digit character: {0}")]
    NonDigitChar(char),

    /// Indicates that the numeric value represented by the BCD number
    /// exceeds the range of `u64`.
    #[error("cannot convert BcdNumber to u64: number too large")]
    Overflow,
}

/// `BcdNumber` is a representation of a numeric value encoded in BCD (Binary Coded Decimal) form.
/// Each byte holds two decimal digits: the upper nibble (4 bits) for the higher digit
/// and the lower nibble (4 bits) for the lower digit. For example, 0x12 represents the digits "1" and "2".
///
/// The internal byte vector is arranged such that the most significant decimal digits are stored
/// toward the start of the vector. Thus, `BcdNumber(vec![0x12, 0x34])` corresponds to the decimal number "1234".
///
/// This type provides conversions to and from `u64`, as well as parsing from strings and raw BCD bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BcdNumber(Vec<u8>);

impl BcdNumber {
    /// Creates a `BcdNumber` from a `u64` value.
    /// Leading zeros are removed except when the value is zero, in which case a single `0x00` byte is used.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcd_convert::BcdNumber;
    ///
    /// let b = BcdNumber::from_u64(1234);
    /// assert_eq!(b.to_string(), "1234");
    /// ```
    pub fn from_u64(mut value: u64) -> Self {
        if value == 0 {
            return BcdNumber(vec![0x00]);
        }

        let mut digits = Vec::new();
        while value > 0 {
            let d = (value % 10) as u8;
            digits.push(d);
            value /= 10;
        }
        digits.reverse();

        let mut bytes = Vec::new();
        if digits.len() == 1 {
            bytes.push(digits[0] & 0x0F);
        } else if digits.len() % 2 == 1 {
            // odd number of digits
            let first = digits[0];
            bytes.push(first);
            for chunk in digits[1..].chunks(2) {
                let hi = chunk[0];
                let lo = chunk[1];
                bytes.push((hi << 4) | lo);
            }
        } else {
            // even number of digits
            for chunk in digits.chunks(2) {
                let hi = chunk[0];
                let lo = chunk[1];
                bytes.push((hi << 4) | lo);
            }
        }

        BcdNumber(bytes)
    }

    /// Creates a `BcdNumber` from a decimal string.
    /// Leading zeros are removed except when the entire string is zero,
    /// in which case a single zero digit is stored.
    ///
    /// Returns `Err(BcdError::NonDigitChar(_))` if any non-digit character is found.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcd_convert::BcdNumber;
    ///
    /// let b = BcdNumber::from_str_strict("001234").unwrap();
    /// assert_eq!(b.to_string(), "1234");
    /// ```
    pub fn from_str_strict(s: &str) -> Result<Self, BcdError> {
        let mut digits: Vec<u8> = Vec::new();
        for c in s.chars() {
            if !c.is_ascii_digit() {
                return Err(BcdError::NonDigitChar(c));
            }
            digits.push(c as u8 - b'0');
        }

        while digits.len() > 1 && digits[0] == 0 {
            digits.remove(0);
        }

        if digits.is_empty() {
            digits.push(0);
        }

        let mut bytes = Vec::new();
        if digits.len() == 1 {
            bytes.push(digits[0] & 0x0F);
        } else if digits.len() % 2 == 1 {
            let first = digits[0];
            bytes.push(first);
            for chunk in digits[1..].chunks(2) {
                bytes.push((chunk[0] << 4) | chunk[1]);
            }
        } else {
            for chunk in digits.chunks(2) {
                bytes.push((chunk[0] << 4) | chunk[1]);
            }
        }

        Ok(BcdNumber(bytes))
    }

    /// Converts this `BcdNumber` into a `u64`.
    ///
    /// Returns `Err(BcdError::InvalidBcdNibble(_))` if the BCD contains invalid digits.
    /// Returns `Err(BcdError::Overflow)` if the number cannot fit into a `u64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcd_convert::BcdNumber;
    ///
    /// let b = BcdNumber::from_u64(9999);
    /// let val = b.to_u64().unwrap();
    /// assert_eq!(val, 9999);
    /// ```
    pub fn to_u64(&self) -> Result<u64, BcdError> {
        let mut result = 0u64;
        for &b in &self.0 {
            let hi = (b >> 4) & 0x0F;
            let lo = b & 0x0F;

            if hi > 9 || lo > 9 {
                return Err(BcdError::InvalidBcdNibble(b));
            }

            let digit_val = (hi as u64) * 10 + (lo as u64);
            let (res, overflow1) = result.overflowing_mul(100);
            let (res, overflow2) = res.overflowing_add(digit_val);
            if overflow1 || overflow2 {
                return Err(BcdError::Overflow);
            }
            result = res;
        }
        Ok(result)
    }

    /// Converts the BCD number into a decimal string.
    ///
    /// This function assumes the internal representation is always valid BCD,
    /// so it never returns an error.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcd_convert::BcdNumber;
    ///
    /// let b = BcdNumber::from_u64(1234);
    /// assert_eq!(b.to_string(), "1234");
    /// ```
    pub fn to_string(&self) -> String {
        let mut s = String::new();
        for &b in &self.0 {
            let hi = (b >> 4) & 0x0F;
            let lo = b & 0x0F;
            s.push((b'0' + hi) as char);
            s.push((b'0' + lo) as char);
        }
        s
    }

    /// Returns the Nth digit of the decimal number, starting from 0 at the leftmost (most significant) digit.
    ///
    /// # Examples
    ///
    /// ```
    /// use bcd_convert::BcdNumber;
    ///
    /// let b = BcdNumber::from_u64(1234);
    /// assert_eq!(b.get_digit(0), Some(1));
    /// assert_eq!(b.get_digit(1), Some(2));
    /// assert_eq!(b.get_digit(2), Some(3));
    /// assert_eq!(b.get_digit(3), Some(4));
    /// assert_eq!(b.get_digit(4), None);
    /// ```
    pub fn get_digit(&self, index: usize) -> Option<u8> {
        let total_digits = self.0.len() * 2;
        if index >= total_digits {
            return None;
        }

        let byte_index = index / 2;
        let nibble_in_byte = index % 2;
        let b = self.0[byte_index];
        let digit = if nibble_in_byte == 0 {
            (b >> 4) & 0x0F
        } else {
            b & 0x0F
        };
        Some(digit)
    }
}

impl FromStr for BcdNumber {
    type Err = BcdError;
    /// Parses a `BcdNumber` from a string slice containing decimal digits.
    ///
    /// Leading zeros are removed except when all digits are zero.
    ///
    /// # Errors
    ///
    /// Returns `Err(BcdError::NonDigitChar(_))` if any character is not a decimal digit.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        BcdNumber::from_str_strict(s)
    }
}

impl fmt::Display for BcdNumber {
    /// Formats the BCD number as a sequence of decimal digits.
    ///
    /// This does not remove leading zeros, as `BcdNumber` maintains a minimal representation internally.
    /// For zero, it will print "00" because a single zero digit is stored as `[0x00]`. You may handle that case
    /// separately if needed.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for &b in &self.0 {
            let hi = (b >> 4) & 0x0F;
            let lo = b & 0x0F;
            write!(f, "{}{}", hi, lo)?;
        }
        Ok(())
    }
}

impl TryFrom<BcdNumber> for u64 {
    type Error = BcdError;
    /// Attempts to convert a `BcdNumber` into a `u64`.
    ///
    /// Returns `Err(BcdError::InvalidBcdNibble(_))` if invalid digits are found,
    /// or `Err(BcdError::Overflow)` if the number is too large for `u64`.
    fn try_from(value: BcdNumber) -> Result<Self, Self::Error> {
        value.to_u64()
    }
}

impl From<u64> for BcdNumber {
    /// Converts a `u64` into a `BcdNumber`.
    fn from(value: u64) -> Self {
        BcdNumber::from_u64(value)
    }
}

impl TryFrom<&[u8]> for BcdNumber {
    type Error = BcdError;
    /// Converts a raw BCD byte slice into a `BcdNumber`.
    ///
    /// This function checks that each nibble is within 0–9.
    /// If invalid data is detected, it returns `Err(BcdError::InvalidBcdNibble(_))`.
    ///
    /// Note: Leading zeros are not stripped here. The provided BCD bytes are stored as is.
    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        let mut digits = Vec::new();
        for &b in value {
            let hi = (b >> 4) & 0x0F;
            let lo = b & 0x0F;
            if hi > 9 || lo > 9 {
                return Err(BcdError::InvalidBcdNibble(b));
            }
            digits.push(hi);
            digits.push(lo);
        }

        Ok(BcdNumber(value.to_vec()))
    }
}

#[cfg(test)]
mod tests {
    use std::vec;

    use super::*;

    #[test]
    fn test_from_u64() {
        assert_eq!(BcdNumber::from_u64(0), BcdNumber(vec![0x00]));
        assert_eq!(BcdNumber::from_u64(1), BcdNumber(vec![0x01]));
        assert_eq!(BcdNumber::from_u64(99), BcdNumber(vec![0x99]));
        assert_eq!(BcdNumber::from_u64(100), BcdNumber(vec![0x01, 0x00]));
        assert_eq!(BcdNumber::from_u64(101), BcdNumber(vec![0x01, 0x01]));
        assert_eq!(BcdNumber::from_u64(1000), BcdNumber(vec![0x10, 0x00]));
        assert_eq!(BcdNumber::from_u64(1234), BcdNumber(vec![0x12, 0x34]));
        assert_eq!(BcdNumber::from_u64(9999), BcdNumber(vec![0x99, 0x99]));
        assert_eq!(
            BcdNumber::from_u64(11010),
            BcdNumber(vec![0x01, 0x10, 0x10])
        );
    }

    #[test]
    fn test_from_str_strict() {
        assert_eq!(
            BcdNumber::from_str_strict("0").unwrap(),
            BcdNumber(vec![0x00])
        );
        assert_eq!(
            BcdNumber::from_str_strict("1").unwrap(),
            BcdNumber(vec![0x01])
        );
        assert_eq!(
            BcdNumber::from_str_strict("99").unwrap(),
            BcdNumber(vec![0x99])
        );
        assert_eq!(
            BcdNumber::from_str_strict("100").unwrap(),
            BcdNumber(vec![0x01, 0x00])
        );
        assert_eq!(
            BcdNumber::from_str_strict("101").unwrap(),
            BcdNumber(vec![0x01, 0x01])
        );
        assert_eq!(
            BcdNumber::from_str_strict("1000").unwrap(),
            BcdNumber(vec![0x10, 0x00])
        );
        assert_eq!(
            BcdNumber::from_str_strict("1234").unwrap(),
            BcdNumber(vec![0x12, 0x34])
        );
        assert_eq!(
            BcdNumber::from_str_strict("9999").unwrap(),
            BcdNumber(vec![0x99, 0x99])
        );
        assert_eq!(
            BcdNumber::from_str_strict("11010").unwrap(),
            BcdNumber(vec![0x01, 0x10, 0x10])
        );
    }

    #[test]
    fn test_from_str_strict_non_digit_char() {
        assert!(matches!(
            BcdNumber::from_str_strict("abcd"),
            Err(BcdError::NonDigitChar('a'))
        ));
    }

    #[test]
    fn test_to_u64() {
        assert_eq!(BcdNumber(vec![0x00]).to_u64().unwrap(), 0);
        assert_eq!(BcdNumber(vec![0x01]).to_u64().unwrap(), 1);
        assert_eq!(BcdNumber(vec![0x99]).to_u64().unwrap(), 99);
        assert_eq!(BcdNumber(vec![0x01, 0x00]).to_u64().unwrap(), 100);
        assert_eq!(BcdNumber(vec![0x01, 0x01]).to_u64().unwrap(), 101);
        assert_eq!(BcdNumber(vec![0x10, 0x00]).to_u64().unwrap(), 1000);
        assert_eq!(BcdNumber(vec![0x12, 0x34]).to_u64().unwrap(), 1234);
        assert_eq!(BcdNumber(vec![0x99, 0x99]).to_u64().unwrap(), 9999);
        assert_eq!(BcdNumber(vec![0x01, 0x10, 0x10]).to_u64().unwrap(), 11010);
    }

    #[test]
    fn test_to_u64_invalid_bcd_nibble() {
        assert!(matches!(
            BcdNumber(vec![0x1A, 0xFF]).to_u64(),
            Err(BcdError::InvalidBcdNibble(0x1A))
        ));
    }

    #[test]
    fn test_to_u64_overflow() {
        assert!(matches!(
            BcdNumber(vec![
                0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
            ])
            .to_u64(),
            Err(BcdError::Overflow)
        ));
    }

    #[test]
    fn test_to_string() {
        assert_eq!(BcdNumber(vec![0x0]).to_string(), "00");
        assert_eq!(BcdNumber(vec![0x00]).to_string(), "00");
        assert_eq!(BcdNumber(vec![0x1]).to_string(), "01");
        assert_eq!(BcdNumber(vec![0x01]).to_string(), "01");
        assert_eq!(BcdNumber(vec![0x99]).to_string(), "99");
        assert_eq!(BcdNumber(vec![0x1, 0x0]).to_string(), "0100");
        assert_eq!(BcdNumber(vec![0x01, 0x00]).to_string(), "0100");
        assert_eq!(BcdNumber(vec![0x1, 0x1]).to_string(), "0101");
        assert_eq!(BcdNumber(vec![0x01, 0x01]).to_string(), "0101");
        assert_eq!(BcdNumber(vec![0x10, 0x00]).to_string(), "1000");
        assert_eq!(BcdNumber(vec![0x12, 0x34]).to_string(), "1234");
        assert_eq!(BcdNumber(vec![0x99, 0x99]).to_string(), "9999");
        assert_eq!(BcdNumber(vec![0x01, 0x10, 0x10]).to_string(), "011010");
    }

    #[test]
    fn test_get_digit() {
        {
            let b = BcdNumber(vec![0x0]);
            assert_eq!(b.get_digit(0), Some(0));
            assert_eq!(b.get_digit(1), Some(0));
            assert_eq!(b.get_digit(2), None);
        }
        {
            let b = BcdNumber(vec![0x00]);
            assert_eq!(b.get_digit(0), Some(0));
            assert_eq!(b.get_digit(1), Some(0));
            assert_eq!(b.get_digit(2), None);
        }
        {
            let b = BcdNumber(vec![0x1]);
            assert_eq!(b.get_digit(0), Some(0));
            assert_eq!(b.get_digit(1), Some(1));
            assert_eq!(b.get_digit(2), None);
        }
        {
            let b = BcdNumber(vec![0x01]);
            assert_eq!(b.get_digit(0), Some(0));
            assert_eq!(b.get_digit(1), Some(1));
            assert_eq!(b.get_digit(2), None);
        }
        {
            let b = BcdNumber(vec![0x99]);
            assert_eq!(b.get_digit(0), Some(9));
            assert_eq!(b.get_digit(1), Some(9));
            assert_eq!(b.get_digit(2), None);
        }
        {
            let b = BcdNumber(vec![0x01, 0x00]);
            assert_eq!(b.get_digit(0), Some(0));
            assert_eq!(b.get_digit(1), Some(1));
            assert_eq!(b.get_digit(2), Some(0));
            assert_eq!(b.get_digit(3), Some(0));
            assert_eq!(b.get_digit(4), None);
        }
        {
            let b = BcdNumber(vec![0x1, 0x00]);
            assert_eq!(b.get_digit(0), Some(0));
            assert_eq!(b.get_digit(1), Some(1));
            assert_eq!(b.get_digit(2), Some(0));
            assert_eq!(b.get_digit(3), Some(0));
            assert_eq!(b.get_digit(4), None);
        }
        {
            let b = BcdNumber(vec![0x01, 0x01]);
            assert_eq!(b.get_digit(0), Some(0));
            assert_eq!(b.get_digit(1), Some(1));
            assert_eq!(b.get_digit(2), Some(0));
            assert_eq!(b.get_digit(3), Some(1));
            assert_eq!(b.get_digit(4), None);
        }
        {
            let b = BcdNumber(vec![0x1, 0x01]);
            assert_eq!(b.get_digit(0), Some(0));
            assert_eq!(b.get_digit(1), Some(1));
            assert_eq!(b.get_digit(2), Some(0));
            assert_eq!(b.get_digit(3), Some(1));
            assert_eq!(b.get_digit(4), None);
        }
        {
            let b = BcdNumber(vec![0x10, 0x00]);
            assert_eq!(b.get_digit(0), Some(1));
            assert_eq!(b.get_digit(1), Some(0));
            assert_eq!(b.get_digit(2), Some(0));
            assert_eq!(b.get_digit(3), Some(0));
            assert_eq!(b.get_digit(4), None);
        }
        {
            let b = BcdNumber(vec![0x12, 0x34]);
            assert_eq!(b.get_digit(0), Some(1));
            assert_eq!(b.get_digit(1), Some(2));
            assert_eq!(b.get_digit(2), Some(3));
            assert_eq!(b.get_digit(3), Some(4));
            assert_eq!(b.get_digit(4), None);
        }
        {
            let b = BcdNumber(vec![0x99, 0x99]);
            assert_eq!(b.get_digit(0), Some(9));
            assert_eq!(b.get_digit(1), Some(9));
            assert_eq!(b.get_digit(2), Some(9));
            assert_eq!(b.get_digit(3), Some(9));
            assert_eq!(b.get_digit(4), None);
        }
        {
            let b = BcdNumber(vec![0x01, 0x10, 0x10]);
            assert_eq!(b.get_digit(0), Some(0));
            assert_eq!(b.get_digit(1), Some(1));
            assert_eq!(b.get_digit(2), Some(1));
            assert_eq!(b.get_digit(3), Some(0));
            assert_eq!(b.get_digit(4), Some(1));
            assert_eq!(b.get_digit(5), Some(0));
            assert_eq!(b.get_digit(6), None);
        }
    }

    #[test]
    fn test_from_str() {
        assert_eq!("0".parse::<BcdNumber>().unwrap(), BcdNumber(vec![0x00]));
        assert_eq!("00".parse::<BcdNumber>().unwrap(), BcdNumber(vec![0x00]));
        assert_eq!("1".parse::<BcdNumber>().unwrap(), BcdNumber(vec![0x01]));
        assert_eq!("01".parse::<BcdNumber>().unwrap(), BcdNumber(vec![0x01]));
        assert_eq!("99".parse::<BcdNumber>().unwrap(), BcdNumber(vec![0x99]));
        assert_eq!(
            "100".parse::<BcdNumber>().unwrap(),
            BcdNumber(vec![0x01, 0x00])
        );
        assert_eq!(
            "0100".parse::<BcdNumber>().unwrap(),
            BcdNumber(vec![0x01, 0x00])
        );
        assert_eq!(
            "101".parse::<BcdNumber>().unwrap(),
            BcdNumber(vec![0x01, 0x01])
        );
        assert_eq!(
            "0101".parse::<BcdNumber>().unwrap(),
            BcdNumber(vec![0x01, 0x01])
        );
        assert_eq!(
            "1234".parse::<BcdNumber>().unwrap(),
            BcdNumber(vec![0x12, 0x34])
        );
        assert_eq!(
            "9999".parse::<BcdNumber>().unwrap(),
            BcdNumber(vec![0x99, 0x99])
        );
        assert_eq!(
            "011010".parse::<BcdNumber>().unwrap(),
            BcdNumber(vec![0x01, 0x10, 0x10])
        );
        assert_eq!(
            "0001234".parse::<BcdNumber>().unwrap(),
            BcdNumber(vec![0x12, 0x34])
        );
    }

    #[test]
    fn test_from_str_error() {
        assert!(matches!(
            BcdNumber::from_str("abcd"),
            Err(BcdError::NonDigitChar('a'))
        ));
        assert!(matches!(
            "abcd".parse::<BcdNumber>(),
            Err(BcdError::NonDigitChar('a'))
        ));
    }

    #[test]
    fn test_try_from_u64() {
        assert_eq!(u64::try_from(BcdNumber(vec![0x0])).unwrap(), 0);
        assert_eq!(u64::try_from(BcdNumber(vec![0x00])).unwrap(), 0);
        assert_eq!(u64::try_from(BcdNumber(vec![0x1])).unwrap(), 1);
        assert_eq!(u64::try_from(BcdNumber(vec![0x01])).unwrap(), 1);
        assert_eq!(u64::try_from(BcdNumber(vec![0x99])).unwrap(), 99);
        assert_eq!(u64::try_from(BcdNumber(vec![0x1, 0x00])).unwrap(), 100);
        assert_eq!(u64::try_from(BcdNumber(vec![0x01, 0x00])).unwrap(), 100);
        assert_eq!(u64::try_from(BcdNumber(vec![0x1, 0x01])).unwrap(), 101);
        assert_eq!(u64::try_from(BcdNumber(vec![0x01, 0x01])).unwrap(), 101);
        assert_eq!(u64::try_from(BcdNumber(vec![0x10, 0x00])).unwrap(), 1000);
        assert_eq!(u64::try_from(BcdNumber(vec![0x12, 0x34])).unwrap(), 1234);
        assert_eq!(u64::try_from(BcdNumber(vec![0x99, 0x99])).unwrap(), 9999);
        assert_eq!(
            u64::try_from(BcdNumber(vec![0x01, 0x10, 0x10])).unwrap(),
            11010
        );
    }

    #[test]
    fn test_try_from_u64_error() {
        assert!(matches!(
            u64::try_from(BcdNumber(vec![0x1A, 0xFF])),
            Err(BcdError::InvalidBcdNibble(0x1A))
        ));
    }

    #[test]
    fn test_from() {
        assert_eq!(BcdNumber::from(0), BcdNumber(vec![0x00]));
        assert_eq!(BcdNumber::from(1), BcdNumber(vec![0x01]));
        assert_eq!(BcdNumber::from(99), BcdNumber(vec![0x99]));
        assert_eq!(BcdNumber::from(100), BcdNumber(vec![0x01, 0x00]));
        assert_eq!(BcdNumber::from(101), BcdNumber(vec![0x01, 0x01]));
        assert_eq!(BcdNumber::from(1000), BcdNumber(vec![0x10, 0x00]));
        assert_eq!(BcdNumber::from(1234), BcdNumber(vec![0x12, 0x34]));
        assert_eq!(BcdNumber::from(9999), BcdNumber(vec![0x99, 0x99]));
        assert_eq!(BcdNumber::from(11010), BcdNumber(vec![0x01, 0x10, 0x10]));
    }

    #[test]
    fn test_try_from_slice() {
        assert_eq!(
            BcdNumber::try_from(&[0x0][..]).unwrap(),
            BcdNumber(vec![0x00])
        );
        assert_eq!(
            BcdNumber::try_from(&[0x00][..]).unwrap(),
            BcdNumber(vec![0x00])
        );
        assert_eq!(
            BcdNumber::try_from(&[0x1][..]).unwrap(),
            BcdNumber(vec![0x01])
        );
        assert_eq!(
            BcdNumber::try_from(&[0x01][..]).unwrap(),
            BcdNumber(vec![0x01])
        );
        assert_eq!(
            BcdNumber::try_from(&[0x99][..]).unwrap(),
            BcdNumber(vec![0x99])
        );
        assert_eq!(
            BcdNumber::try_from(&[0x1, 0x00][..]).unwrap(),
            BcdNumber(vec![0x01, 0x00])
        );
        assert_eq!(
            BcdNumber::try_from(&[0x01, 0x00][..]).unwrap(),
            BcdNumber(vec![0x01, 0x00])
        );
        assert_eq!(
            BcdNumber::try_from(&[0x1, 0x01][..]).unwrap(),
            BcdNumber(vec![0x01, 0x01])
        );
        assert_eq!(
            BcdNumber::try_from(&[0x01, 0x01][..]).unwrap(),
            BcdNumber(vec![0x01, 0x01])
        );
        assert_eq!(
            BcdNumber::try_from(&[0x10, 0x00][..]).unwrap(),
            BcdNumber(vec![0x10, 0x00])
        );
        assert_eq!(
            BcdNumber::try_from(&[0x12, 0x34][..]).unwrap(),
            BcdNumber(vec![0x12, 0x34])
        );
        assert_eq!(
            BcdNumber::try_from(&[0x99, 0x99][..]).unwrap(),
            BcdNumber(vec![0x99, 0x99])
        );
        assert_eq!(
            BcdNumber::try_from(&[0x01, 0x10, 0x10][..]).unwrap(),
            BcdNumber(vec![0x01, 0x10, 0x10])
        );
    }

    #[test]
    fn test_try_from_slice_invalid_bcd_nibble() {
        assert!(matches!(
            BcdNumber::try_from(&[0xA][..]),
            Err(BcdError::InvalidBcdNibble(0xA))
        ));
    }

    #[test]
    fn test_format() {
        let b = BcdNumber(vec![0x01]);
        let s = format!("Hello, {} !!", b); // s = "Hello, Rust !!"
        println!("{}", s);
    }
}
