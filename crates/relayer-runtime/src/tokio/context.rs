use alloc::sync::Arc;
use async_trait::async_trait;
use core::fmt::Debug;
use core::future::Future;
use core::marker::PhantomData;
use core::time::Duration;
use std::sync::Mutex;
use std::time::Instant;
use tokio::runtime::Runtime;
use tokio::sync::{mpsc, oneshot};
use tokio::time::sleep;
use tracing;

use ibc_relayer_framework::base::core::traits::sync::Async;
use ibc_relayer_framework::base::one_for_all::traits::chain::OfaBaseChain;
use ibc_relayer_framework::base::one_for_all::traits::runtime::{LogLevel, OfaRuntime};
use ibc_relayer_framework::full::one_for_all::traits::batch::OfaBatch;

use super::error::Error as TokioError;

pub struct TokioRuntimeContext<Error> {
    pub runtime: Arc<Runtime>,
    pub phantom: PhantomData<Error>,
}

impl<Error> TokioRuntimeContext<Error> {
    pub fn new(runtime: Arc<Runtime>) -> Self {
        Self {
            runtime,
            phantom: PhantomData,
        }
    }
}

impl<Error> Clone for TokioRuntimeContext<Error> {
    fn clone(&self) -> Self {
        Self::new(self.runtime.clone())
    }
}

#[async_trait]
impl<Error> OfaRuntime for TokioRuntimeContext<Error>
where
    Error: From<TokioError> + Debug + Async,
{
    type Error = Error;

    type Time = Instant;

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
}

#[async_trait]
impl<Chain, Error> OfaBatch<Chain> for TokioRuntimeContext<Error>
where
    Chain: OfaBaseChain<Error = Error>,
    Error: From<TokioError> + Clone + Async,
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

    async fn send_batch(
        sender: &Self::BatchSender,
        messages: Vec<Chain::Message>,
        result_sender: Self::ResultSender,
    ) -> Result<(), Chain::Error> {
        sender
            .send((messages, result_sender))
            .map_err(|_| TokioError::channel_closed().into())
    }

    async fn try_receive_batch(
        receiver_lock: &Self::BatchReceiver,
    ) -> Result<Option<(Vec<Chain::Message>, Self::ResultSender)>, Chain::Error> {
        let mut receiver = receiver_lock
            .lock()
            .map_err(|_| TokioError::poisoned_lock())?;

        match receiver.try_recv() {
            Ok(batch) => Ok(Some(batch)),
            Err(mpsc::error::TryRecvError::Empty) => Ok(None),
            Err(mpsc::error::TryRecvError::Disconnected) => {
                Err(TokioError::channel_closed().into())
            }
        }
    }

    async fn receive_result(
        result_receiver: Self::ResultReceiver,
    ) -> Result<Result<Vec<Vec<Chain::Event>>, Chain::Error>, Chain::Error> {
        result_receiver
            .await
            .map_err(|_| TokioError::channel_closed().into())
    }

    fn send_result(
        result_sender: Self::ResultSender,
        events: Result<Vec<Vec<Chain::Event>>, Chain::Error>,
    ) -> Result<(), Chain::Error> {
        result_sender
            .send(events)
            .map_err(|_| TokioError::channel_closed().into())
    }
}
