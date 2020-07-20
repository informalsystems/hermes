//! TryFromRaw trait for automatic protobuf deserialization - currently implemented with prost
//! This is similar to the pattern of using the #[serde(from="RawType") derive for automatic
//! conversion with the TryFrom::try_from<InternalType>(value: RawType) trait for validation.
//! Only serde does this for JSON and here we need to do it for protobuf.
use crate::error::{Error, Kind};
use bytes::Bytes;
use prost::Message;
use std::convert::Into;
use std::default::Default;
use std::error::Error as StdError;
use std::marker::Sized;
use std::vec::Vec;

/// TryFromRaw trait needs to implement a try_from() function and an Error type for the return of that function.
pub trait TryFromRaw: Sized {
    /// RawType defines the prost-compiled protobuf-defined Rust struct
    type RawType: Message + Default;

    /// Error defines the error type returned from validation.
    type Error: Into<Box<dyn StdError + Send + Sync + 'static>>;

    /// try_from function will validate the incoming RawType and convert it to our domain type
    fn try_from(value: Self::RawType) -> Result<Self, Self::Error>;

    /// deserialize function will deserialize from the protobuf-encoded bytes into the domain type
    /// using the RawType and try_from() as an interim step.
    fn deserialize(wire: Vec<u8>) -> Result<Self, Error> {
        Self::RawType::decode(Bytes::from(wire))
            .map_err(|e| Kind::ResponseParsing.context(e).into())
            .and_then(|r| Self::try_from(r).map_err(|e| Kind::ResponseParsing.context(e).into()))
    }
}
