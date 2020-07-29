//! TryFromRaw trait for automatic protobuf deserialization - currently implemented with prost
//! This is similar to the pattern of using the #[serde(from="RawType") derive for automatic
//! conversion with the TryFrom::try_from<InternalType>(value: RawType) trait for validation.
//! Only serde does this for JSON and here we need to do it for protobuf.
use prost::Message;
use std::convert::Into;
use std::default::Default;
use std::error::Error as StdError;
use std::marker::Sized;

/// TryFromRaw trait needs to implement a try_from() function and an Error type for the return of that function.
pub trait TryFromRaw: Sized {
    /// RawType defines the prost-compiled protobuf-defined Rust struct
    type RawType: Message + Default;

    /// Error defines the error type returned from validation.
    type Error: Into<Box<dyn StdError + Send + Sync + 'static>>;

    /// try_from function will validate the incoming RawType and convert it to our domain type
    fn try_from(value: Self::RawType) -> Result<Self, Self::Error>;
}
