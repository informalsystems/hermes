use core::future::Future;
use core::pin::Pin;
use core::time::Duration;
use std::time::Instant;

use async_trait::async_trait;
use futures::lock::{Mutex, MutexGuard};
use futures::stream::Stream;
use ibc_relayer_all_in_one::one_for_all::traits::runtime::OfaRuntime;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components_extra::runtime::traits::spawn::TaskHandle;
use tokio::sync::{mpsc, oneshot};
use tokio::time::sleep;
use tokio_stream::wrappers::UnboundedReceiverStream;

use crate::types::error::Error;
use crate::types::runtime::TokioRuntimeContext;
use crate::types::task::TokioTaskHandle;

#[async_trait]
impl OfaRuntime for TokioRuntimeContext {
    type Error = Error;

    type Time = Instant;

    type Mutex<T: Async> = Mutex<T>;

    type MutexGuard<'a, T: Async> = MutexGuard<'a, T>;

    type Sender<T> = mpsc::UnboundedSender<T>
    where
        T: Async;

    type Receiver<T> = mpsc::UnboundedReceiver<T>
    where
        T: Async;

    type SenderOnce<T> = oneshot::Sender<T>
    where
        T: Async;

    type ReceiverOnce<T> = oneshot::Receiver<T>
    where
        T: Async;

    async fn sleep(&self, duration: Duration) {
        sleep(duration).await;
    }

    fn now(&self) -> Instant {
        Instant::now()
    }

    fn duration_since(time: &Instant, other: &Instant) -> Duration {
        time.duration_since(*other)
    }

    fn new_mutex<T: Async>(item: T) -> Self::Mutex<T> {
        Mutex::new(item)
    }

    async fn acquire_mutex<'a, T: Async>(mutex: &'a Self::Mutex<T>) -> Self::MutexGuard<'a, T> {
        mutex.lock().await
    }

    fn spawn<F>(&self, task: F) -> Box<dyn TaskHandle>
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        let join_handle = self.runtime.spawn(async move {
            task.await;
        });
        Box::new(TokioTaskHandle(join_handle))
    }

    fn new_channel<T>() -> (Self::Sender<T>, Self::Receiver<T>)
    where
        T: Async,
    {
        mpsc::unbounded_channel()
    }

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

    fn receiver_to_stream<T>(
        receiver: Self::Receiver<T>,
    ) -> Pin<Box<dyn Stream<Item = T> + Send + 'static>>
    where
        T: Async,
    {
        Box::pin(UnboundedReceiverStream::new(receiver))
    }

    fn new_channel_once<T>() -> (Self::SenderOnce<T>, Self::ReceiverOnce<T>)
    where
        T: Async,
    {
        let (sender, receiver) = oneshot::channel();
        (sender, receiver)
    }

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

impl TaskHandle for TokioTaskHandle {
    fn abort(self: Box<Self>) {
        self.0.abort();
    }

    fn into_future(self: Box<Self>) -> Pin<Box<dyn Future<Output = ()> + Send + 'static>> {
        Box::pin(async move {
            let _ = self.0.await;
        })
    }
}
