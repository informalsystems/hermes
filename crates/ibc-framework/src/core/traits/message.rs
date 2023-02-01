use crate::core::traits::sync::Async;

pub trait HasMessageTypes {
    type Message: Async;

    type MessageType: Eq + Async;

    type Signer: Async;
}

pub trait HasMessageMethods: HasMessageTypes {
    fn message_type(message: &Self::Message) -> Self::MessageType;
}
