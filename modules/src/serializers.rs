#[cfg(feature="prusti")]
use prusti_contracts::*;

use serde::ser::{Serialize, Serializer};
use subtle_encoding::{Encoding, Hex};

#[cfg_attr(feature="prusti", requires(Hex::upper_case().encode_to_string(data).is_ok()))]
pub fn ser_hex_upper<S, T>(data: T, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
    T: AsRef<[u8]>,
{
    let hex = Hex::upper_case().encode_to_string(data).unwrap();
    hex.serialize(serializer)
}
