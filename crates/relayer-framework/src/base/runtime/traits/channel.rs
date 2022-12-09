use async_trait::async_trait;

use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

pub trait HasChannelTypes: HasErrorType {
    type Sender<T>
    where
        T: Async;

    type Receiver<T>
    where
        T: Async;
}

pub trait CanCreateChannels: HasChannelTypes {
    fn new_channel<T>() -> (Self::Sender<T>, Self::Receiver<T>)
    where
        T: Async;
}

#[async_trait]
pub trait CanUseChannelsOnce: CanCreateChannels {
    fn send_once<T>(sender: Self::Sender<T>, value: T)
    where
        T: Async;

    async fn receive_once<T>(receiver: Self::Receiver<T>) -> Result<T, Self::Error>
    where
        T: Async;
}

#[async_trait]
pub trait CanUseChannels: CanCreateChannels {
    fn send<T>(sender: Self::Sender<T>, value: T) -> Result<(), Self::Error>
    where
        T: Async;

    async fn receive<T>(receiver: Self::Receiver<T>) -> Result<T, Self::Error>
    where
        T: Async;

    async fn try_receive<T>(receiver: Self::Receiver<T>) -> Result<Option<T>, Self::Error>
    where
        T: Async;
}
