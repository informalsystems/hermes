use core::pin::Pin;

use async_trait::async_trait;
use futures::Stream;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components_extra::runtime::traits::channel::{
    CanCreateChannels, CanStreamReceiver, CanUseChannels, HasChannelTypes,
};
use ibc_relayer_components_extra::runtime::traits::channel_once::{
    CanCreateChannelsOnce, CanUseChannelsOnce, HasChannelOnceTypes,
};
use tokio::sync::{mpsc, oneshot};
use tokio_stream::wrappers::UnboundedReceiverStream;

use crate::types::error::Error;
use crate::types::runtime::TokioRuntimeContext;

impl HasChannelTypes for TokioRuntimeContext {
    type Sender<T> = mpsc::UnboundedSender<T>
    where
        T: Async;

    type Receiver<T> = mpsc::UnboundedReceiver<T>
    where
        T: Async;
}

impl HasChannelOnceTypes for TokioRuntimeContext {
    type SenderOnce<T> = oneshot::Sender<T>
    where
        T: Async;

    type ReceiverOnce<T> = oneshot::Receiver<T>
    where
        T: Async;
}

impl CanCreateChannels for TokioRuntimeContext {
    fn new_channel<T>() -> (Self::Sender<T>, Self::Receiver<T>)
    where
        T: Async,
    {
        mpsc::unbounded_channel()
    }
}

impl CanCreateChannelsOnce for TokioRuntimeContext {
    fn new_channel_once<T>() -> (Self::SenderOnce<T>, Self::ReceiverOnce<T>)
    where
        T: Async,
    {
        let (sender, receiver) = oneshot::channel();
        (sender, receiver)
    }
}

#[async_trait]
impl CanUseChannels for TokioRuntimeContext {
    fn send<T>(sender: &Self::Sender<T>, value: T) -> Result<(), Self::Error>
    where
        T: Async,
    {
        sender.send(value).map_err(|_| Error::channel_closed())
    }

    async fn receive<T>(receiver: &mut Self::Receiver<T>) -> Result<T, Self::Error>
    where
        T: Async,
    {
        receiver.recv().await.ok_or_else(Error::channel_closed)
    }

    fn try_receive<T>(receiver: &mut Self::Receiver<T>) -> Result<Option<T>, Self::Error>
    where
        T: Async,
    {
        match receiver.try_recv() {
            Ok(batch) => Ok(Some(batch)),
            Err(mpsc::error::TryRecvError::Empty) => Ok(None),
            Err(mpsc::error::TryRecvError::Disconnected) => Err(Error::channel_closed()),
        }
    }
}

#[async_trait]
impl CanUseChannelsOnce for TokioRuntimeContext {
    fn send_once<T>(sender: Self::SenderOnce<T>, value: T) -> Result<(), Self::Error>
    where
        T: Async,
    {
        sender.send(value).map_err(|_| Error::channel_closed())
    }

    async fn receive_once<T>(receiver: Self::ReceiverOnce<T>) -> Result<T, Self::Error>
    where
        T: Async,
    {
        receiver.await.map_err(|_| Error::channel_closed())
    }
}

impl CanStreamReceiver for TokioRuntimeContext {
    fn receiver_to_stream<T>(
        receiver: Self::Receiver<T>,
    ) -> Pin<Box<dyn Stream<Item = T> + Send + 'static>>
    where
        T: Async,
    {
        Box::pin(UnboundedReceiverStream::new(receiver))
    }
}
