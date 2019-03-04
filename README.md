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