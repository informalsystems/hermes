use bytes::Buf;
use prost::{DecodeError, Message};
use std::convert::TryFrom;

pub enum Error<TryFromError> {
    Decode(DecodeError),
    TryFrom(TryFromError),
}

pub fn decode_protobuf<Raw, Payload, B, E>(buf: B) -> Result<Payload, Error<E>>
where
    Raw: Message,
    Raw: Default,
    Payload: TryFrom<Raw, Error = E>,
    B: Buf,
{
    Raw::decode(buf).map_or_else(
        |e| Err(Error::Decode(e)),
        |t| Payload::try_from(t).map_err(Error::TryFrom),
    )
}
