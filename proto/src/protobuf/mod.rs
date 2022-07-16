mod error;

use core::fmt::Display;

use bytes::Buf;
use prost::encoding::encoded_len_varint;
use prost::Message;

pub use error::Error;

mod sealed {
    pub trait SealedToBoxed<T: ?Sized> {}
    impl<T, U: Clone + Into<T>> SealedToBoxed<T> for U {}
    pub trait SealedTryFromIfSized<T> {}
    impl<T, U: TryFrom<T>> SealedTryFromIfSized<T> for U {}
}

pub trait ToBoxed<T: ?Sized>: sealed::SealedToBoxed<T> {
    fn to_boxed(&self) -> Box<T>;
}

impl<T, U: Clone + Into<T>> ToBoxed<T> for U {
    fn to_boxed(&self) -> Box<T> {
        Box::new(self.clone().into())
    }
}

pub trait TryFromIfSized<T>: sealed::SealedTryFromIfSized<T> {
    type Error;

    fn try_from(t: T) -> Result<Self, Self::Error>
    where
        Self: Sized;
}

impl<T, U: TryFrom<T>> TryFromIfSized<T> for U {
    type Error = <Self as TryFrom<T>>::Error;

    fn try_from(t: T) -> Result<Self, Self::Error>
    where
        Self: Sized,
    {
        <Self as TryFrom<T>>::try_from(t)
    }
}

pub trait Protobuf<T: Message + Default>
where
    Self: TryFromIfSized<T> + ToBoxed<T>,
    <Self as TryFromIfSized<T>>::Error: Display,
{
    /// Encode into a buffer in Protobuf format.
    ///
    /// Uses [`prost::Message::encode`] after converting into its counterpart
    /// Protobuf data structure.
    ///
    /// [`prost::Message::encode`]: https://docs.rs/prost/*/prost/trait.Message.html#method.encode
    fn encode(&self, buf: &mut Vec<u8>) -> Result<(), Error> {
        self.to_boxed().encode(buf).map_err(Error::encode_message)
    }

    /// Encode with a length-delimiter to a buffer in Protobuf format.
    ///
    /// An error will be returned if the buffer does not have sufficient capacity.
    ///
    /// Uses [`prost::Message::encode_length_delimited`] after converting into
    /// its counterpart Protobuf data structure.
    ///
    /// [`prost::Message::encode_length_delimited`]: https://docs.rs/prost/*/prost/trait.Message.html#method.encode_length_delimited
    fn encode_length_delimited(&self, buf: &mut Vec<u8>) -> Result<(), Error> {
        self.to_boxed()
            .encode_length_delimited(buf)
            .map_err(Error::encode_message)
    }

    /// Constructor that attempts to decode an instance from a buffer.
    ///
    /// The entire buffer will be consumed.
    ///
    /// Similar to [`prost::Message::decode`] but with additional validation
    /// prior to constructing the destination type.
    ///
    /// [`prost::Message::decode`]: https://docs.rs/prost/*/prost/trait.Message.html#method.decode
    fn decode<B: Buf>(buf: B) -> Result<Self, Error>
    where
        Self: Sized,
    {
        let raw = T::decode(buf).map_err(Error::decode_message)?;

        Self::try_from(raw).map_err(Error::try_from::<T, Self, _>)
    }

    /// Constructor that attempts to decode a length-delimited instance from
    /// the buffer.
    ///
    /// The entire buffer will be consumed.
    ///
    /// Similar to [`prost::Message::decode_length_delimited`] but with
    /// additional validation prior to constructing the destination type.
    ///
    /// [`prost::Message::decode_length_delimited`]: https://docs.rs/prost/*/prost/trait.Message.html#method.decode_length_delimited
    fn decode_length_delimited<B: Buf>(buf: B) -> Result<Self, Error>
    where
        Self: Sized,
    {
        let raw = T::decode_length_delimited(buf).map_err(Error::decode_message)?;

        Self::try_from(raw).map_err(Error::try_from::<T, Self, _>)
    }

    /// Returns the encoded length of the message without a length delimiter.
    ///
    /// Uses [`prost::Message::encoded_len`] after converting to its
    /// counterpart Protobuf data structure.
    ///
    /// [`prost::Message::encoded_len`]: https://docs.rs/prost/*/prost/trait.Message.html#method.encoded_len
    fn encoded_len(&self) -> usize {
        self.to_boxed().encoded_len()
    }

    /// Encodes into a Protobuf-encoded `Vec<u8>`.
    fn encode_vec(&self) -> Result<Vec<u8>, Error> {
        let mut wire = Vec::with_capacity(self.encoded_len());
        self.encode(&mut wire).map(|_| wire)
    }

    /// Constructor that attempts to decode a Protobuf-encoded instance from a
    /// `Vec<u8>` (or equivalent).
    fn decode_vec(v: &[u8]) -> Result<Self, Error>
    where
        Self: Sized,
    {
        Self::decode(v)
    }

    /// Encode with a length-delimiter to a `Vec<u8>` Protobuf-encoded message.
    fn encode_length_delimited_vec(&self) -> Result<Vec<u8>, Error> {
        let len = self.encoded_len();
        let lenu64 = len.try_into().map_err(Error::parse_length)?;
        let mut wire = Vec::with_capacity(len + encoded_len_varint(lenu64));
        self.encode_length_delimited(&mut wire).map(|_| wire)
    }

    /// Constructor that attempts to decode a Protobuf-encoded instance with a
    /// length-delimiter from a `Vec<u8>` or equivalent.
    fn decode_length_delimited_vec(v: &[u8]) -> Result<Self, Error>
    where
        Self: Sized,
    {
        Self::decode_length_delimited(v)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::google::protobuf::Any;

    #[test]
    fn test_protobuf_object_safety() {
        let _test: Option<Box<dyn Protobuf<Any, Error = Error>>> = None;
    }

    #[test]
    fn test_protobuf_blanket_impls() {
        trait Foo: Protobuf<Any, Error = Error> {}

        #[derive(Clone)]
        struct Domain;

        impl Foo for Domain {}

        impl Protobuf<Any> for Domain {}

        impl TryFrom<Any> for Domain {
            type Error = Error;

            fn try_from(_: Any) -> Result<Self, Self::Error> {
                unimplemented!()
            }
        }

        impl From<Domain> for Any {
            fn from(_: Domain) -> Self {
                unimplemented!()
            }
        }
    }
}
