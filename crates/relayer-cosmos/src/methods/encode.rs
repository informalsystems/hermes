use ibc_proto::google::protobuf::Any;
use prost::{EncodeError, Message as ProstMessage};

pub fn encode_message<Message>(message: &Message) -> Result<Vec<u8>, EncodeError>
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
    let encoded_message = encode_message(message)?;

    let any_message = Any {
        type_url: type_url.to_string(),
        value: encoded_message,
    };

    Ok(any_message)
}
