use serde::ser::{Serialize, Serializer};
use subtle_encoding::{Encoding, Hex};

pub fn ser_hex_upper<S, T>(data: T, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
    T: AsRef<[u8]>,
{
    let hex = Hex::upper_case().encode_to_string(data).unwrap();
    hex.serialize(serializer)
}

pub mod serde_string {
    use alloc::string::String;
    use core::fmt::Display;
    use core::str::FromStr;

    use serde::{de, Deserialize, Deserializer, Serializer};

    pub fn serialize<T, S>(value: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        T: Display,
        S: Serializer,
    {
        serializer.collect_str(value)
    }

    pub fn deserialize<'de, T, D>(deserializer: D) -> Result<T, D::Error>
    where
        T: FromStr,
        T::Err: Display,
        D: Deserializer<'de>,
    {
        String::deserialize(deserializer)?
            .parse()
            .map_err(de::Error::custom)
    }
}
