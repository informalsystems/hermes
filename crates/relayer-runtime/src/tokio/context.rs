use alloc::sync::Arc;
use core::future::Future;
use core::pin::Pin;
use core::time::Duration;
use futures::channel::{mpsc, oneshot};
use futures::lock::{Mutex, MutexGuard};
use futures::stream::StreamExt;
use std::time::Instant;

use async_trait::async_trait;
use futures::stream::Stream;
use ibc_relayer_all_in_one::base::one_for_all::traits::runtime::OfaBaseRuntime;
use ibc_relayer_all_in_one::base::one_for_all::types::runtime::LogLevel;
use ibc_relayer_all_in_one::extra::one_for_all::traits::runtime::OfaFullRuntime;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components_extra::runtime::traits::spawn::TaskHandle;
use tokio::runtime::Runtime;
use tokio::task::JoinHandle;
use tokio::time::sleep;
use tracing;

use super::error::Error as TokioError;

pub struct TokioRuntimeContext {
    pub runtime: Arc<Runtime>,
}

pub struct TokioTaskHandle(pub JoinHandle<()>);

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
        mpsc::unbounded()
    }

    fn send<T>(sender: &Self::Sender<T>, value: T) -> Result<(), Self::Error>
    where
        T: Async,
    {
        sender
            .unbounded_send(value)
            .map_err(|_| TokioError::channel_closed())
    }

    async fn receive<T>(receiver: &mut Self::Receiver<T>) -> Result<T, Self::Error>
    where
        T: Async,
    {
        receiver.next().await.ok_or_else(TokioError::channel_closed)
    }

    fn try_receive<T>(receiver: &mut Self::Receiver<T>) -> Result<Option<T>, Self::Error>
    where
        T: Async,
    {
        match receiver.try_next() {
            Ok(batch) => Ok(batch),
            Err(_) => Err(TokioError::channel_closed()),
        }
    }

    fn receiver_to_stream<T>(
        receiver: Self::Receiver<T>,
    ) -> Pin<Box<dyn Stream<Item = T> + Send + 'static>>
    where
        T: Async,
    {
        Box::pin(receiver)
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
