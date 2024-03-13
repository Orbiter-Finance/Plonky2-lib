pub mod stream;
extern crate hex;

#[macro_export]
macro_rules! bytes {
    ($hex_literal:expr) => {{
        let hex_string = $hex_literal;
        let stripped = if let Some(stripped) = hex_string.strip_prefix("0x") {
            stripped
        } else {
            &hex_string
        };
        hex::decode(stripped)
            .expect("Invalid hex string")
            .try_into()
            .expect(&format!(
                "Wrong byte length {} for hex string {}",
                stripped.len(),
                hex_string
            ))
    }};
}
