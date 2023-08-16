use core::fmt::Debug;
use core::ops::DerefMut;
use core::pin::Pin;
use core::time::Duration;

use async_trait::async_trait;
use futures_core::{Future, Stream};
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components_extra::runtime::traits::spawn::TaskHandle;

use crate::std_prelude::*;

#[async_trait]
pub trait OfaRuntime: Async {
    type Error: Async + Debug;

    type Time: Async;

    type Mutex<T: Async>: Async;

    type MutexGuard<'a, T: Async>: 'a + Send + Sync + DerefMut<Target = T>;

    type Sender<T>: Clone + Async
    where
        T: Async;

    type Receiver<T>: Async
    where
        T: Async;

    type SenderOnce<T>: Async
    where
        T: Async;

    type ReceiverOnce<T>: Async
    where
        T: Async;

    async fn sleep(&self, duration: Duration);

    fn now(&self) -> Self::Time;

    fn duration_since(time: &Self::Time, other: &Self::Time) -> Duration;

    fn new_mutex<T: Async>(item: T) -> Self::Mutex<T>;

    async fn acquire_mutex<'a, T: Async>(mutex: &'a Self::Mutex<T>) -> Self::MutexGuard<'a, T>;

    fn spawn<F>(&self, task: F) -> Box<dyn TaskHandle>
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static;

    fn new_channel<T>() -> (Self::Sender<T>, Self::Receiver<T>)
    where
        T: Async;

    fn send<T>(sender: &Self::Sender<T>, value: T) -> Result<(), Self::Error>
    where
        T: Async;

    async fn receive<T>(receiver: &mut Self::Receiver<T>) -> Result<T, Self::Error>
    where
        T: Async;

    fn try_receive<T>(receiver: &mut Self::Receiver<T>) -> Result<Option<T>, Self::Error>
    where
        T: Async;

    fn receiver_to_stream<T>(
        receiver: Self::Receiver<T>,
    ) -> Pin<Box<dyn Stream<Item = T> + Send + 'static>>
    where
        T: Async;

    fn new_channel_once<T>() -> (Self::SenderOnce<T>, Self::ReceiverOnce<T>)
    where
        T: Async;

    fn send_once<T>(sender: Self::SenderOnce<T>, value: T) -> Result<(), Self::Error>
    where
        T: Async;

    async fn receive_once<T>(receiver: Self::ReceiverOnce<T>) -> Result<T, Self::Error>
    where
        T: Async;
}
