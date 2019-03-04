#[cfg(test)]
mod tests {
    use super::{
        convert_to_bytes, convert_to_bytes_base_10, convert_to_bytes_base_2, ConversionError,
    };
    #[test]
    fn test_kb_uppercase() {
        assert_eq!(1000_u128, convert_to_bytes("1 KB").unwrap());
    }

    #[test]
    fn test_kb_lowercase() {
        assert_eq!(1000_u128, convert_to_bytes("1 kb").unwrap());
    }

    #[test]
    fn test_kb_mixedcase() {
        assert_eq!(1000_u128, convert_to_bytes("1 kB").unwrap());
    }

    #[test]
    fn test_kib() {
        assert_eq!(1024_u128, convert_to_bytes("1 KiB").unwrap());
    }

    #[test]
    fn test_mb() {
        assert_eq!(1_000_000_u128, convert_to_bytes("1 MB").unwrap());
    }

    #[test]
    fn test_gb() {
        assert_eq!(1_000_000_000_u128, convert_to_bytes("1 GB").unwrap());
    }

    #[test]
    fn test_tb() {
        assert_eq!(1_000_000_000_000_u128, convert_to_bytes("1 TB").unwrap());
    }

    #[test]
    fn test_pb() {
        assert_eq!(
            1_000_000_000_000_000_u128,
            convert_to_bytes("1 PB").unwrap()
        );
    }

    #[test]
    fn test_eb() {
        assert_eq!(
            1_000_000_000_000_000_000_u128,
            convert_to_bytes("1 EB").unwrap()
        );
    }

    #[test]
    fn test_zb() {
        assert_eq!(
            1_000_000_000_000_000_000_000_u128,
            convert_to_bytes("1 ZB").unwrap()
        );
    }

    #[test]
    fn test_yb() {
        assert_eq!(
            1_000_000_000_000_000_000_000_000_u128,
            convert_to_bytes("1 YB").unwrap()
        );
    }

    #[test]
    fn test_decimal() {
        assert_eq!(
            9_108_079_886_394_091_110_u128,
            convert_to_bytes("7.9 EiB").unwrap()
        );
    }

    #[test]
    fn test_no_space() {
        assert_eq!(1024, convert_to_bytes("1KiB").unwrap());
    }

    #[test]
    fn test_forced_bases() {
        assert_eq!(1000, convert_to_bytes_base_10("1KiB").unwrap());
        assert_eq!(1024, convert_to_bytes_base_2("1KB").unwrap());
    }

    #[test]
    fn test_too_large() {
        match convert_to_bytes("281474976710657 YiB") {
            Err(ConversionError::TooLarge) => return,
            _ => panic!("Did not get a TooLarge error"),
        }
    }

    #[test]
    fn test_invalid() {
        match convert_to_bytes("invalid input") {
            Err(ConversionError::InputInvalid(_)) => return,
            _ => panic!("Did not get an InputInvalid error"),
        }
    }

    #[test]
    fn test_invalid_units() {
        match convert_to_bytes("1 bad unit") {
            Err(ConversionError::InputInvalid(_)) => (),
            _ => panic!("Did not get an InputInvalid error"),
        }
        match convert_to_bytes("1 kilobadunit") {
            Err(ConversionError::InputInvalid(_)) => (),
            _ => panic!("Did not get an InputInvalid error"),
        }
        match convert_to_bytes("1kbu") {
            Err(ConversionError::InputInvalid(_)) => (return),
            _ => panic!("Did not get an InputInvalid error"),
        }
    }
}

/// Represents possible errors the library can return.
#[derive(Debug)]
pub enum ConversionError {
    /// The provided input could not be parsed; more details may be available in the String.
    InputInvalid(String),
    /// The provided input was parsed correctly, but the output was too large to fit in a u128.
    TooLarge,
}

/// Stores a number as either an i128 or an f64
enum ParsingNumber {
    Int(u128),
    Float((u128, u128)),
}

/// Represent whether the conversion should be forced to base 10, base 2, or implied
enum ForceBase {
    Base2,
    Base10,
    Implied,
}

/// Convert the provided string to a u128 value containing the number of bytes represented by the string.
/// Implies the base to use based on the string, e.g. "KiB" uses base 2 and "KB" uses base 10.
///
/// # Arguments
///
/// * `string` - The string to convert.
///
/// # Returns
///
/// * `Err(ConversionError::InputInvalid)` if the input was invalid. The String may contain more information.
/// * `Err(ConversionError::TooLarge)` if the
///
/// # Example
///
/// ```rust
/// use convert_byte_size_string::convert_to_bytes;
/// assert_eq!(1024_u128, convert_to_bytes("1KiB").expect("a"));
/// assert_eq!(1000_u128, convert_to_bytes("1KB").expect("b"));
/// ```
pub fn convert_to_bytes(string: &str) -> Result<u128, ConversionError> {
    convert_to_bytes_with_base(string, ForceBase::Implied)
}

/// Like `convert_to_bytes` but forces the units to be treated as base 10 units (multiples of 1000).
pub fn convert_to_bytes_base_10(string: &str) -> Result<u128, ConversionError> {
    convert_to_bytes_with_base(string, ForceBase::Base10)
}

/// Like `convert_to_bytes` but forces the units to be treated as base 2 units (multiples of 1024).
pub fn convert_to_bytes_base_2(string: &str) -> Result<u128, ConversionError> {
    convert_to_bytes_with_base(string, ForceBase::Base2)
}

fn convert_to_bytes_with_base(string: &str, base: ForceBase) -> Result<u128, ConversionError> {
    let lowercase = string.to_lowercase();
    let mut splits: Vec<&str> = lowercase.trim().split_whitespace().collect();
    if splits.len() < 2 {
        splits.clear();
        let (index, _) = match lowercase
            .trim()
            .match_indices(|c: char| {
                c == 'k'
                    || c == 'm'
                    || c == 'g'
                    || c == 't'
                    || c == 'p'
                    || c == 'e'
                    || c == 'z'
                    || c == 'y'
            })
            .next()
        {
            Some(val) => val,
            None => {
                return Err(ConversionError::InputInvalid(String::from(
                    "Did not find two parts in string",
                )));
            }
        };

        splits.push(&lowercase[..index]);
        splits.push(&lowercase[index..]);
    }

    let mantissa: ParsingNumber;
    match splits[0].parse::<u128>() {
        Ok(n) => mantissa = ParsingNumber::Int(n),
        Err(_) => {
            let float_splits: Vec<&str> = splits[0].split('.').collect();
            if float_splits.len() != 2 {
                return Err(ConversionError::InputInvalid(format!(
                    "Could not parse '{}' into an i128 or an f64",
                    splits[0]
                )));
            }

            let whole = match float_splits[0].parse::<u128>() {
                Ok(val) => val,
                Err(_) => {
                    return Err(ConversionError::InputInvalid(format!(
                        "Could not parse '{}' into an i128 or an f64",
                        splits[0]
                    )));
                }
            };
            let fraction = match float_splits[1].parse::<u128>() {
                Ok(val) => val,
                Err(_) => {
                    return Err(ConversionError::InputInvalid(format!(
                        "Could not parse '{}' into an i128 or an f64",
                        splits[0]
                    )));
                }
            };
            mantissa = ParsingNumber::Float((whole, fraction));
        }
    }

    let exponent = parse_exponent(splits[1], base)?;

    match mantissa {
        ParsingNumber::Int(m) => match m.checked_mul(exponent) {
            Some(val) => Ok(val),
            None => Err(ConversionError::TooLarge),
        },
        ParsingNumber::Float(m) => {
            if let Some(whole) = m.0.checked_mul(exponent) {
                if let Some(fraction) = m.1.checked_mul(exponent) {
                    if let Some(fraction) = fraction.checked_div(10) {
                        if let Some(val) = whole.checked_add(fraction) {
                            return Ok(val);
                        }
                    }
                }
            }
            Err(ConversionError::TooLarge)
        }
    }
}

/// Parse the correct exponent to use based on the string.
fn parse_exponent(string: &str, base: ForceBase) -> Result<u128, ConversionError> {
    if !string.is_ascii() {
        return Err(ConversionError::InputInvalid(format!(
            "Could not parse '{}' because it contains invalid characters",
            string
        )));
    }

    let chars: Vec<char> = string.to_lowercase().chars().collect();
    if chars.len() < 2 {
        return Err(ConversionError::InputInvalid(String::from(
            "Unit not long enough",
        )));
    }

    let base_1000: u128 = match base {
        ForceBase::Implied => match chars[1] {
            'b' if chars.len() == 2 => 1000,
            'i' if chars.len() > 2 && chars[2] == 'b' => 1024,
            _ if chars[2] == 'b' => {
                return Err(ConversionError::InputInvalid(format!(
                    "Invalid character in unit: {}",
                    chars[1]
                )));
            }
            _ => {
                return Err(ConversionError::InputInvalid(format!(
                    "Invalid unit: {}",
                    string
                )));
            }
        },
        ForceBase::Base10 => 1000,
        ForceBase::Base2 => 1024,
    };

    let exponent: u128 = match chars[0] {
        'k' => base_1000,
        'm' => base_1000 * base_1000,
        'g' => base_1000 * base_1000 * base_1000,
        't' => base_1000 * base_1000 * base_1000 * base_1000,
        'p' => base_1000 * base_1000 * base_1000 * base_1000 * base_1000,
        'e' => base_1000 * base_1000 * base_1000 * base_1000 * base_1000 * base_1000,
        'z' => base_1000 * base_1000 * base_1000 * base_1000 * base_1000 * base_1000 * base_1000,
        'y' => {
            base_1000
                * base_1000
                * base_1000
                * base_1000
                * base_1000
                * base_1000
                * base_1000
                * base_1000
        }
        _ => {
            return Err(ConversionError::InputInvalid(format!(
                "Invalid character in unit: {}",
                chars[0]
            )));
        }
    };

    Ok(exponent)
}
