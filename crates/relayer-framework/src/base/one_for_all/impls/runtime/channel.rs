use async_trait::async_trait;

use crate::base::core::traits::sync::Async;
use crate::base::one_for_all::traits::runtime::{OfaRuntime, OfaRuntimeWrapper};
use crate::base::runtime::traits::channel::{
    CanCreateChannels, CanUseChannels, CanUseChannelsOnce, HasChannelTypes,
};
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

#[async_trait]
impl<Runtime> CanUseChannelsOnce for OfaRuntimeWrapper<Runtime>
where
    Runtime: OfaRuntime,
{
    fn send_once<T>(sender: Self::Sender<T>, value: T) -> Result<(), Self::Error>
    where
        T: Async,
    {
        Runtime::send(&sender, value)
    }

    async fn receive_once<T>(receiver: Self::Receiver<T>) -> Result<T, Self::Error>
    where
        T: Async,
    {
        Runtime::receive(&receiver).await
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

    async fn receive<T>(receiver: &Self::Receiver<T>) -> Result<T, Self::Error>
    where
        T: Async,
    {
        Runtime::receive(receiver).await
    }

    async fn try_receive<T>(receiver: &Self::Receiver<T>) -> Result<Option<T>, Self::Error>
    where
        T: Async,
    {
        Runtime::try_receive(receiver).await
    }
}
