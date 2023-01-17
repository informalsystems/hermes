use alloc::sync::Arc;
use async_trait::async_trait;
use core::future::Future;
use core::pin::Pin;
use core::time::Duration;
use futures::stream::Stream;
use std::time::Instant;
use tokio::runtime::Runtime;
use tokio::sync::{mpsc, oneshot, Mutex, MutexGuard};
use tokio::time::sleep;
use tokio_stream::wrappers::UnboundedReceiverStream;
use tracing;

use ibc_relayer_framework::base::core::traits::sync::Async;
use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaBaseRuntime;
use ibc_relayer_framework::base::one_for_all::types::runtime::LogLevel;
use ibc_relayer_framework::full::one_for_all::traits::runtime::OfaFullRuntime;

use super::error::Error as TokioError;

pub struct TokioRuntimeContext {
    pub runtime: Arc<Runtime>,
}

impl TokioRuntimeContext {
    pub fn new(runtime: Arc<Runtime>) -> Self {
        Self { runtime }
    }
}

#[async_trait]
impl OfaBaseRuntime for TokioRuntimeContext {
    type Error = TokioError;

    type Time = Instant;

    type Mutex<T: Async> = Mutex<T>;

    type MutexGuard<'a, T: Async> = MutexGuard<'a, T>;

    async fn log(&self, level: LogLevel, message: &str) {
        match level {
            LogLevel::Error => tracing::error!(message),
            LogLevel::Warn => tracing::warn!(message),
            LogLevel::Info => tracing::info!(message),
            LogLevel::Debug => tracing::debug!(message),
            LogLevel::Trace => tracing::trace!(message),
        }
    }

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
}

#[async_trait]
impl OfaFullRuntime for TokioRuntimeContext {
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

    fn spawn<F>(&self, task: F)
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        self.runtime.spawn(task);
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
        sender.send(value).map_err(|_| TokioError::channel_closed())
    }

    async fn receive<T>(receiver: &mut Self::Receiver<T>) -> Result<T, Self::Error>
    where
        T: Async,
    {
        receiver.recv().await.ok_or_else(TokioError::channel_closed)
    }

    fn try_receive<T>(receiver: &mut Self::Receiver<T>) -> Result<Option<T>, Self::Error>
    where
        T: Async,
    {
        match receiver.try_recv() {
            Ok(batch) => Ok(Some(batch)),
            Err(mpsc::error::TryRecvError::Empty) => Ok(None),
            Err(mpsc::error::TryRecvError::Disconnected) => Err(TokioError::channel_closed()),
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
        sender.send(value).map_err(|_| TokioError::channel_closed())
    }

    async fn receive_once<T>(receiver: Self::ReceiverOnce<T>) -> Result<T, Self::Error>
    where
        T: Async,
    {
        receiver.await.map_err(|_| TokioError::channel_closed())
    }
}
