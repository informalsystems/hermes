use crate::prelude::*;
use serde::{
	ser::{Serialize, Serializer},
	Deserialize, Deserializer,
};
use subtle_encoding::{Encoding, Hex};

pub fn ser_hex_upper<S, T>(data: T, serializer: S) -> Result<S::Ok, S::Error>
where
	S: Serializer,
	T: AsRef<[u8]>,
{
	let hex = Hex::upper_case().encode_to_string(data).unwrap();
	hex.serialize(serializer)
}

pub fn deser_hex_upper<'de, T, D>(deserializer: D) -> Result<T, D::Error>
where
	D: Deserializer<'de>,
	T: AsRef<[u8]>,
	T: From<Vec<u8>>,
{
	let hex = String::deserialize(deserializer)?;
	let bytes = Hex::upper_case().decode(hex.as_bytes()).unwrap();
	Ok(bytes.into())
}

pub mod serde_string {
	use alloc::string::String;
	use core::{fmt::Display, str::FromStr};

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
		String::deserialize(deserializer)?.parse().map_err(de::Error::custom)
	}
}
