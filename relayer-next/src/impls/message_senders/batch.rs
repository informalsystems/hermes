use async_trait::async_trait;
use tokio::sync::mpsc::Sender;
use tokio::sync::oneshot::{channel as once_channel, error::RecvError, Sender as OnceSender};

use crate::traits::chain_context::IbcChainContext;
use crate::traits::core::Async;
use crate::traits::ibc_message_sender::IbcMessageSender;
use crate::traits::relay_context::RelayContext;
use crate::traits::target::ChainTarget;

pub struct SendError {
    pub message: String,
}

pub struct BatchedMessageSender;

pub struct MessageSink<Message, Event, Error> {
    sender: Sender<(Vec<Message>, OnceSender<Result<Vec<Vec<Event>>, Error>>)>,
}

pub trait HasMessageSink<Message, Event, Error> {
    fn message_sink(&self) -> &MessageSink<Message, Event, Error>;
}

#[async_trait]
impl<Context, Target, TargetChain, Message, Event, Error> IbcMessageSender<Context, Target>
    for BatchedMessageSender
where
    Message: Async,
    Event: Async,
    Error: Async,
    Error: From<SendError>,
    Error: From<RecvError>,
    Context: RelayContext<Error = Error>,
    Context: HasMessageSink<Message, Event, Error>,
    Target: ChainTarget<Context, TargetChain = TargetChain>,
    TargetChain: IbcChainContext<Target::CounterpartyChain, IbcMessage = Message, IbcEvent = Event>,
{
    async fn send_messages(
        context: &Context,
        messages: Vec<Message>,
    ) -> Result<Vec<Vec<Event>>, Context::Error> {
        let (sender, receiver) = once_channel();

        context
            .message_sink()
            .sender
            .send((messages, sender))
            .await
            .map_err(|e| SendError {
                message: e.to_string(),
            })?;

        let events = receiver.await??;

        Ok(events)
    }
}
