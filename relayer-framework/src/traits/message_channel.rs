use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::error::HasError;
use crate::traits::core::Async;

pub trait HasChannel: Async {
    type ChannelContext: Async;
}

pub trait BaseChannelContext<T>: HasError {
    type Sender: Async;
    type Receiver: Async;

    fn new_channel() -> (Self::Sender, Self::Receiver);
}

#[async_trait]
pub trait SenderContext<T>: BaseChannelContext<T> {
    async fn send(sender: &Self::Sender, message: T) -> Result<(), Self::Error>;
}

#[async_trait]
pub trait SenderOnceContext<T>: BaseChannelContext<T> {
    async fn send_once(sender: Self::Sender, message: T) -> Result<(), Self::Error>;
}

#[async_trait]
pub trait ReceiverContext<T>: BaseChannelContext<T> {
    async fn receive(receiver: &Self::Receiver) -> Result<T, Self::Error>;
}

#[async_trait]
pub trait TryReceiverContext<T>: BaseChannelContext<T> {
    async fn try_receive(receiver: &Self::Receiver) -> Result<Option<T>, Self::Error>;
}

#[async_trait]
pub trait ReceiverOnceContext<T>: BaseChannelContext<T> {
    async fn receive_once(receiver: Self::Receiver) -> Result<T, Self::Error>;
}

pub trait MultiChannelContext<T>:
    SenderContext<T>
    + SenderOnceContext<T>
    + TryReceiverContext<T>
    + ReceiverContext<T>
    + ReceiverOnceContext<T>
{
}

pub trait OnceChannelContext<T>: SenderOnceContext<T> + ReceiverOnceContext<T> {}

impl<Channel, T> MultiChannelContext<T> for Channel where
    Channel: SenderContext<T>
        + SenderOnceContext<T>
        + TryReceiverContext<T>
        + ReceiverContext<T>
        + ReceiverOnceContext<T>
{
}

impl<Channel, T> OnceChannelContext<T> for Channel where
    Channel:
        SenderContext<T> + SenderOnceContext<T> + SenderOnceContext<T> + ReceiverOnceContext<T>
{
}
