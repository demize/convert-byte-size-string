# convert-byte-size-string

This crate provides functionality to convert an arbitrary byte size string such as "7.9 EiB" into a `u128` value usable wherever you need it.

## Usage

Add the following to your `Cargo.toml`:

```toml
[dependencies]
convert-byte-size-string = "1.0"
```

In your code, you can:

```rust
use convert_byte_size_string::convert_to_bytes;

let size: u128 = convert_to_bytes("7.9 EiB").unwrap();
```

## Features

This library has a fairly basic set of features:

- Convert byte size strings to u128 values based on the unit in the string, interpreting the unit as either a base 2 unit or a base 10 unit
- Convert byte size strings based on the unit in the string, forcing the unit to be treated as either base 10 or base 2