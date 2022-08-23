use alloc::sync::Arc;
use async_trait::async_trait;
use core::future::Future;
use core::marker::PhantomData;
use core::time::Duration;
use ibc_relayer_framework::impls::message_senders::batch::context::BatchContext;
use ibc_relayer_framework::one_for_all::traits::error::OfaError;
use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntime;
use ibc_relayer_framework::traits::core::Async;
use std::time::Instant;
use tokio::runtime::Runtime;
use tokio::sync::{mpsc, oneshot};
use tokio::time::sleep;

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
    Error: OfaError + From<TokioError>,
{
    type Error = Error;

    type Time = Instant;

    async fn sleep(&self, duration: Duration) {
        sleep(duration).await;
    }

    fn now(&self) -> Instant {
        Instant::now()
    }

    fn duration_since(time: &Instant, other: &Instant) -> Duration {
        time.duration_since(other.clone())
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
impl<Message, Event, Error> BatchContext<Message, Event> for TokioRuntimeContext<Error>
where
    Message: Async,
    Event: Async,
    Error: From<TokioError> + Clone + Async,
{
    type Error = Error;

    type MessagesSender = mpsc::Sender<(Vec<Message>, Self::ResultSender)>;
    type MessagesReceiver = mpsc::Receiver<(Vec<Message>, Self::ResultSender)>;

    type ResultSender = oneshot::Sender<Result<Vec<Vec<Event>>, Error>>;
    type ResultReceiver = oneshot::Receiver<Result<Vec<Vec<Event>>, Error>>;

    fn new_messages_channel(&self) -> (Self::MessagesSender, Self::MessagesReceiver) {
        mpsc::channel(1024)
    }

    fn new_result_channel(&self) -> (Self::ResultSender, Self::ResultReceiver) {
        oneshot::channel()
    }

    async fn send_messages(
        sender: &Self::MessagesSender,
        messages: Vec<Message>,
        result_sender: Self::ResultSender,
    ) -> Result<(), Error> {
        sender
            .send((messages, result_sender))
            .await
            .map_err(|_| TokioError::channel_closed().into())
    }

    async fn try_receive_messages(
        receiver: &mut Self::MessagesReceiver,
    ) -> Result<Option<(Vec<Message>, Self::ResultSender)>, Error> {
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
    ) -> Result<Result<Vec<Vec<Event>>, Error>, Error> {
        result_receiver
            .await
            .map_err(|_| TokioError::channel_closed().into())
    }

    fn send_result(
        result_sender: Self::ResultSender,
        events: Result<Vec<Vec<Event>>, Error>,
    ) -> Result<(), Error> {
        result_sender
            .send(events)
            .map_err(|_| TokioError::channel_closed().into())
    }
}
