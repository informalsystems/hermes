use alloc::boxed::Box;
use alloc::sync::Arc;
use async_trait::async_trait;
use core::{future::Future, time::Duration};
use ibc_relayer_framework::base::core::traits::sync::Async;
use tokio::sync::{mpsc, oneshot, Mutex};

use crate::relayer_mock::base::types::aliases::MockTimestamp;
use crate::relayer_mock::util::clock::MockClock;

use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntime;
use ibc_relayer_framework::base::one_for_all::types::runtime::LogLevel;
use ibc_relayer_runtime::tokio::error::Error as TokioError;

pub struct MockRuntimeContext {
    pub clock: Arc<MockClock>,
}

impl MockRuntimeContext {
    pub fn new(clock: Arc<MockClock>) -> Self {
        Self { clock }
    }

    pub fn get_time(&self) -> MockTimestamp {
        self.clock.get_timestamp()
    }
}

impl Clone for MockRuntimeContext {
    fn clone(&self) -> Self {
        let clock = self.clock.clone();
        Self::new(clock)
    }
}

#[async_trait]
impl OfaRuntime for MockRuntimeContext {
    type Error = TokioError;

    type Time = MockTimestamp;

    type Sender<T> = mpsc::UnboundedSender<T>
    where
        T: Async;

    type Receiver<T> = Arc<Mutex<mpsc::UnboundedReceiver<T>>>
    where
        T: Async;

    type SenderOnce<T> = oneshot::Sender<T>
    where
        T: Async;

    type ReceiverOnce<T> = oneshot::Receiver<T>
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

    // Increment the shared MockClock by the duration is milliseconds.
    async fn sleep(&self, duration: Duration) {
        if self.clock.increment_millis(duration.as_millis()).is_err() {
            tracing::warn!("MockClock failed to sleep for {}ms", duration.as_millis());
        }
    }

    fn now(&self) -> Self::Time {
        self.get_time()
    }

    fn duration_since(time: &Self::Time, other: &Self::Time) -> Duration {
        Duration::from_millis((time - other) as u64)
    }

    fn spawn<F>(&self, task: F)
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        tokio::spawn(task);
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
        sender.send(value).map_err(|_| TokioError::channel_closed())
    }

    async fn receive<T>(receiver_lock: &Self::Receiver<T>) -> Result<T, Self::Error>
    where
        T: Async,
    {
        let mut receiver = receiver_lock.lock().await;

        receiver.recv().await.ok_or_else(TokioError::channel_closed)
    }

    async fn try_receive<T>(receiver_lock: &Self::Receiver<T>) -> Result<Option<T>, Self::Error>
    where
        T: Async,
    {
        let mut receiver = receiver_lock.lock().await;

        match receiver.try_recv() {
            Ok(batch) => Ok(Some(batch)),
            Err(mpsc::error::TryRecvError::Empty) => Ok(None),
            Err(mpsc::error::TryRecvError::Disconnected) => Err(TokioError::channel_closed()),
        }
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
