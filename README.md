# bcd-convert

A Rust library for working with Binary Coded Decimal (BCD) values. This crate provides utilities for converting between numeric types (such as `u64`) and BCD-encoded data, as well as parsing and formatting BCD values from and into strings.

## Features

- **BCD Parsing and Formatting**: Convert BCD data into integers and vice versa.
- **String Integration**: Parse `BcdNumber` from decimal strings and format them back.
- **Error Handling**: Returns descriptive errors if invalid BCD data is encountered or if conversions overflow the target integer type.
- **Standard Traits**:
  - Implements `FromStr` and `Display` for `BcdNumber`, enabling `"1234".parse::<BcdNumber>()` and `format!()` usage.
  - Implements `TryFrom`/`TryInto` for conversion to and from `u64`.

## Example

```rust
use std::convert::TryFrom;
use bcd_convert::BcdNumber;

// From u64
let bcd_val = BcdNumber::from_u64(1234);
assert_eq!(bcd_val.to_string(), "1234");

// To u64
let val = bcd_val.to_u64().unwrap();
assert_eq!(val, 1234);

// From string with leading zeros removed
let parsed = "0001234".parse::<BcdNumber>().unwrap();
assert_eq!(parsed.to_string(), "1234");

// Handling zero
assert_eq!("0".parse::<BcdNumber>().unwrap(), BcdNumber(vec![0x00]));
assert_eq!(BcdNumber::from(0), BcdNumber(vec![0x00]));

// Understanding single-digit scenarios
// Here, 0x1 means the top nibble is 0 and the bottom nibble is 1, so "01"
let b = BcdNumber(vec![0x1]);
assert_eq!(b.get_digit(0), Some(0));
assert_eq!(b.get_digit(1), Some(1));
assert_eq!(b.get_digit(2), None);

// Similarly, 0x01 means "01" as well.
let b = BcdNumber(vec![0x01]);
assert_eq!(b.get_digit(0), Some(0));
assert_eq!(b.get_digit(1), Some(1));
assert_eq!(b.get_digit(2), None);

// From raw BCD bytes
let raw_bcd = &[0x12, 0x34];
let from_bytes = BcdNumber::try_from(raw_bcd).unwrap();
assert_eq!(from_bytes.to_string(), "1234");

// Error handling: invalid nibble
let invalid = &[0x1A]; // 0xA is not a valid BCD digit
assert!(matches!(BcdNumber::try_from(invalid), Err(bcd_convert::BcdError::InvalidBcdNibble(0x1A))));

// Overflow check
let big_str = "999999999999999999999"; // Too large for u64
let big_num = big_str.parse::<BcdNumber>().unwrap();
assert!(matches!(big_num.to_u64(), Err(bcd_convert::BcdError::Overflow)));
```

## Installation

Add bcd-convert to your Cargo.toml:

```toml
[dependencies]
bcd-convert = "0.1.0"
```

Then run cargo build to fetch and build the library.

## Documentation

Visit [Docs.rs](https://docs.rs/) once the crate is published, or run cargo doc --open locally to view the generated documentation.

## License

This project is licensed under the [MIT License](https://github.com/hiroakis/bcd-convert/blob/main/LICENSE).
