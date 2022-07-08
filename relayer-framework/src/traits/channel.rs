use async_trait::async_trait;
use tokio::sync::mpsc::{channel, error::TryRecvError, Receiver, Sender};

use crate::std_prelude::*;

pub trait BaseChannelContext<T> {
    type Sender;
    type Receiver;

    type SendError;
    type ReceiveError;

    fn create_channel(buffer_size: usize) -> (Self::Sender, Self::Receiver);
}

#[async_trait]
pub trait SenderContext<T>: BaseChannelContext<T> {
    async fn send(sender: &Self::Sender, message: T) -> Result<(), Self::SendError>;
}

#[async_trait]
pub trait SenderOnceContext<T>: BaseChannelContext<T> {
    async fn send_once(sender: Self::Sender, message: T) -> Result<(), Self::SendError>;
}

#[async_trait]
pub trait ReceiverContext<T>: BaseChannelContext<T> {
    async fn receive(receiver: &mut Self::Receiver) -> Result<T, Self::ReceiveError>;
}

#[async_trait]
pub trait TryReceiverContext<T>: BaseChannelContext<T> {
    fn try_receive(receiver: &mut Self::Receiver) -> Result<Option<T>, Self::ReceiveError>;
}

#[async_trait]
pub trait ReceiverOnceContext<T>: BaseChannelContext<T> {
    async fn receive_once(receiver: Self::Receiver) -> Result<T, Self::ReceiveError>;
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

pub struct TokioChannel;
pub struct TokioOnceChannel;

pub struct ChannelClosedError;

impl<T> BaseChannelContext<T> for TokioChannel {
    type Sender = Sender<T>;
    type Receiver = Receiver<T>;

    type SendError = ChannelClosedError;
    type ReceiveError = ChannelClosedError;

    fn create_channel(buffer_size: usize) -> (Sender<T>, Receiver<T>) {
        channel(buffer_size)
    }
}

#[async_trait]
impl<T> SenderContext<T> for TokioChannel
where
    T: Send,
{
    async fn send(sender: &Self::Sender, message: T) -> Result<(), Self::SendError> {
        sender.send(message).await.map_err(|_| ChannelClosedError)
    }
}

#[async_trait]
impl<T> SenderOnceContext<T> for TokioChannel
where
    T: Send + 'static,
{
    async fn send_once(sender: Self::Sender, message: T) -> Result<(), Self::SendError> {
        sender.send(message).await.map_err(|_| ChannelClosedError)
    }
}

#[async_trait]
impl<T> ReceiverContext<T> for TokioChannel
where
    T: Send,
{
    async fn receive(receiver: &mut Self::Receiver) -> Result<T, Self::ReceiveError> {
        receiver.recv().await.ok_or(ChannelClosedError)
    }
}

#[async_trait]
impl<T> TryReceiverContext<T> for TokioChannel
where
    T: Send,
{
    fn try_receive(receiver: &mut Self::Receiver) -> Result<Option<T>, Self::ReceiveError> {
        match receiver.try_recv() {
            Ok(message) => Ok(Some(message)),
            Err(TryRecvError::Empty) => Ok(None),
            Err(TryRecvError::Disconnected) => Err(ChannelClosedError),
        }
    }
}

#[async_trait]
impl<T> ReceiverOnceContext<T> for TokioChannel
where
    T: Send + 'static,
{
    async fn receive_once(mut receiver: Self::Receiver) -> Result<T, Self::ReceiveError> {
        receiver.recv().await.ok_or(ChannelClosedError)
    }
}
