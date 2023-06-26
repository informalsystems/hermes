use core::pin::Pin;

use async_trait::async_trait;
use futures_core::stream::Stream;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components_extra::runtime::traits::channel::{
    CanCreateChannels, CanStreamReceiver, CanUseChannels, HasChannelTypes,
};
use ibc_relayer_components_extra::runtime::traits::channel_once::{
    CanCreateChannelsOnce, CanUseChannelsOnce, HasChannelOnceTypes,
};

use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::std_prelude::*;

impl<Runtime> HasChannelTypes for OfaRuntimeWrapper<Runtime>
where
    Runtime: OfaRuntime,
{
    type Sender<T> = Runtime::Sender<T>
    where
        T: Async;

    type Receiver<T> = Runtime::Receiver<T>
    where
        T: Async;
}

impl<Runtime> HasChannelOnceTypes for OfaRuntimeWrapper<Runtime>
where
    Runtime: OfaRuntime,
{
    type SenderOnce<T> = Runtime::SenderOnce<T>
    where
        T: Async;

    type ReceiverOnce<T> = Runtime::ReceiverOnce<T>
    where
        T: Async;
}

impl<Runtime> CanCreateChannels for OfaRuntimeWrapper<Runtime>
where
    Runtime: OfaRuntime,
{
    fn new_channel<T>() -> (Self::Sender<T>, Self::Receiver<T>)
    where
        T: Async,
    {
        Runtime::new_channel()
    }
}

impl<Runtime> CanCreateChannelsOnce for OfaRuntimeWrapper<Runtime>
where
    Runtime: OfaRuntime,
{
    fn new_channel_once<T>() -> (Self::SenderOnce<T>, Self::ReceiverOnce<T>)
    where
        T: Async,
    {
        Runtime::new_channel_once()
    }
}

#[async_trait]
impl<Runtime> CanUseChannelsOnce for OfaRuntimeWrapper<Runtime>
where
    Runtime: OfaRuntime,
{
    fn send_once<T>(sender: Self::SenderOnce<T>, value: T) -> Result<(), Self::Error>
    where
        T: Async,
    {
        Runtime::send_once(sender, value)
    }

    async fn receive_once<T>(receiver: Self::ReceiverOnce<T>) -> Result<T, Self::Error>
    where
        T: Async,
    {
        Runtime::receive_once(receiver).await
    }
}

#[async_trait]
impl<Runtime> CanUseChannels for OfaRuntimeWrapper<Runtime>
where
    Runtime: OfaRuntime,
{
    fn send<T>(sender: &Self::Sender<T>, value: T) -> Result<(), Self::Error>
    where
        T: Async,
    {
        Runtime::send(sender, value)
    }

    async fn receive<T>(receiver: &mut Self::Receiver<T>) -> Result<T, Self::Error>
    where
        T: Async,
    {
        Runtime::receive(receiver).await
    }

    fn try_receive<T>(receiver: &mut Self::Receiver<T>) -> Result<Option<T>, Self::Error>
    where
        T: Async,
    {
        Runtime::try_receive(receiver)
    }
}

impl<Runtime> CanStreamReceiver for OfaRuntimeWrapper<Runtime>
where
    Runtime: OfaRuntime,
{
    fn receiver_to_stream<T>(
        receiver: Self::Receiver<T>,
    ) -> Pin<Box<dyn Stream<Item = T> + Send + 'static>>
    where
        T: Async,
    {
        Runtime::receiver_to_stream(receiver)
    }
}
