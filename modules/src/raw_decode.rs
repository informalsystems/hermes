//! RawDecode trait for automatic protobuf deserialization - currently implemented with prost
//! This is similar to the pattern of using the #[serde(from="RawType") derive for automatic
//! conversion with the TryFrom::try_from<InternalType>(value: RawType) trait for validation.
//! Only serde does this for JSON and here we need to do it with protobuf.
use bytes::Bytes;
use prost::{DecodeError, Message};
use std::convert::Into;
use std::default::Default;
use std::error::Error;
use std::marker::Sized;
use std::vec::Vec;

/// RawDecode trait needs to implement a validate() function and an Error type for the return of that function.
pub trait RawDecode: Sized {
    /// RawType defines the prost-compiled protobuf-defined Rust struct
    type RawType: Message + Default;

    /// Error defines the error type returned from validation.
    type Error: Into<Box<dyn Error + Send + Sync + 'static>>;

    /// validate function will validate the incoming RawType and convert it to our internal type
    fn validate(value: Self::RawType) -> Result<Self, Self::Error>;

    /// raw_decode function will decode the type from RawType using Prost
    fn raw_decode(wire: Vec<u8>) -> Result<Self::RawType, DecodeError> {
        Self::RawType::decode(Bytes::from(wire))
    }
}
