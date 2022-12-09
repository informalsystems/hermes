use alloc::sync::Arc;
use async_trait::async_trait;
use core::future::Future;
use core::time::Duration;
use std::time::Instant;
use tokio::runtime::Runtime;
use tokio::sync::Mutex;
use tokio::sync::{mpsc, oneshot};
use tokio::time::sleep;
use tracing;

use ibc_relayer_framework::base::core::traits::sync::Async;
use ibc_relayer_framework::base::one_for_all::traits::chain::OfaBaseChain;
use ibc_relayer_framework::base::one_for_all::traits::runtime::{LogLevel, OfaRuntime};
use ibc_relayer_framework::full::one_for_all::traits::batch::OfaBatch;

use super::error::Error as TokioError;

#[derive(Clone)]
pub struct TokioRuntimeContext {
    pub runtime: Arc<Runtime>,
}

impl TokioRuntimeContext {
    pub fn new(runtime: Arc<Runtime>) -> Self {
        Self { runtime }
    }
}

#[async_trait]
impl OfaRuntime for TokioRuntimeContext {
    type Error = TokioError;

    type Time = Instant;

    type Sender<T> = mpsc::UnboundedSender<T>
    where
        T: Async;

    type Receiver<T> = Arc<Mutex<mpsc::UnboundedReceiver<T>>>
    where
        T: Async;

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
        let (sender, receiver) = mpsc::unbounded_channel();
        (sender, Arc::new(Mutex::new(receiver)))
    }

    fn send<T>(sender: &Self::Sender<T>, value: T) -> Result<(), Self::Error>
    where
        T: Async,
    {
        sender
            .send(value)
            .map_err(|_| TokioError::channel_closed().into())
    }

    async fn receive<T>(receiver_lock: &Self::Receiver<T>) -> Result<T, Self::Error>
    where
        T: Async,
    {
        let mut receiver = receiver_lock.lock().await;

        receiver
            .recv()
            .await
            .ok_or_else(|| TokioError::channel_closed().into())
    }

    async fn try_receive<T>(receiver_lock: &Self::Receiver<T>) -> Result<Option<T>, Self::Error>
    where
        T: Async,
    {
        let mut receiver = receiver_lock.lock().await;

        match receiver.try_recv() {
            Ok(batch) => Ok(Some(batch)),
            Err(mpsc::error::TryRecvError::Empty) => Ok(None),
            Err(mpsc::error::TryRecvError::Disconnected) => {
                Err(TokioError::channel_closed().into())
            }
        }
    }
}

#[async_trait]
impl<Chain> OfaBatch<Chain> for TokioRuntimeContext
where
    Chain: OfaBaseChain<Runtime = Self>,
{
    type BatchSender = mpsc::UnboundedSender<(Vec<Chain::Message>, Self::ResultSender)>;
    type BatchReceiver =
        Arc<Mutex<mpsc::UnboundedReceiver<(Vec<Chain::Message>, Self::ResultSender)>>>;

    type ResultSender = oneshot::Sender<Result<Vec<Vec<Chain::Event>>, Chain::Error>>;
    type ResultReceiver = oneshot::Receiver<Result<Vec<Vec<Chain::Event>>, Chain::Error>>;

    fn new_batch_channel() -> (Self::BatchSender, Self::BatchReceiver) {
        let (sender, receiver) = mpsc::unbounded_channel();

        (sender, Arc::new(Mutex::new(receiver)))
    }

    fn new_result_channel() -> (Self::ResultSender, Self::ResultReceiver) {
        oneshot::channel()
    }

    fn send_batch(
        sender: &Self::BatchSender,
        messages: Vec<Chain::Message>,
        result_sender: Self::ResultSender,
    ) -> Result<(), Chain::Error> {
        sender
            .send((messages, result_sender))
            .map_err(|_| Chain::runtime_error(TokioError::channel_closed()))
    }

    async fn try_receive_batch(
        receiver_lock: &Self::BatchReceiver,
    ) -> Result<Option<(Vec<Chain::Message>, Self::ResultSender)>, Chain::Error> {
        let mut receiver = receiver_lock.lock().await;

        match receiver.try_recv() {
            Ok(batch) => Ok(Some(batch)),
            Err(mpsc::error::TryRecvError::Empty) => Ok(None),
            Err(mpsc::error::TryRecvError::Disconnected) => {
                Err(Chain::runtime_error(TokioError::channel_closed()))
            }
        }
    }

    async fn receive_result(
        result_receiver: Self::ResultReceiver,
    ) -> Result<Result<Vec<Vec<Chain::Event>>, Chain::Error>, Chain::Error> {
        result_receiver
            .await
            .map_err(|_| Chain::runtime_error(TokioError::channel_closed()))
    }

    fn send_result(
        result_sender: Self::ResultSender,
        events: Result<Vec<Vec<Chain::Event>>, Chain::Error>,
    ) -> Result<(), Chain::Error> {
        result_sender
            .send(events)
            .map_err(|_| Chain::runtime_error(TokioError::channel_closed()))
    }
}
