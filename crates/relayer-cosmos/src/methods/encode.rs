//! Helper functions for encoding protobuf messages into bytes.

use ibc_proto::google::protobuf::Any;
use prost::{EncodeError, Message as ProstMessage};

pub fn encode_protobuf<Message>(message: &Message) -> Result<Vec<u8>, EncodeError>
where
    Message: ProstMessage,
{
    let mut buf = Vec::new();
    Message::encode(message, &mut buf)?;
    Ok(buf)
}

pub fn encode_to_any<Message>(type_url: &str, message: &Message) -> Result<Any, EncodeError>
where
    Message: ProstMessage,
{
    let encoded_message = encode_protobuf(message)?;

    let any_message = Any {
        type_url: type_url.to_string(),
        value: encoded_message,
    };

    Ok(any_message)
}

pub fn encode_any_to_bytes<Message>(
    type_url: &str,
    message: &Message,
) -> Result<Vec<u8>, EncodeError>
where
    Message: ProstMessage,
{
    let any = encode_to_any(type_url, message)?;

    let bytes = encode_protobuf(&any)?;

    Ok(bytes)
}
