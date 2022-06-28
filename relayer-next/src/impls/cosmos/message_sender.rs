use async_trait::async_trait;
use ibc::events::IbcEvent;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::tracking::TrackedMsgs;

use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::handler::{CosmosChainHandler, CosmosRelayHandler};
use crate::impls::cosmos::message::CosmosIbcMessage;
use crate::impls::cosmos::target::CosmosChainTarget;
use crate::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::traits::chain_context::{ChainContext, IbcChainContext};
use crate::traits::ibc_message_sender::IbcMessageSenderContext;
use crate::traits::message::Message;
use crate::traits::message_sender::{MessageSender, MessageSenderContext};
use crate::traits::target::ChainTarget;

pub struct CosmosBaseMessageSender;

impl<SrcChain, DstChain, Target> IbcMessageSenderContext<Target>
    for CosmosRelayHandler<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
    Target: ChainTarget<CosmosRelayHandler<SrcChain, DstChain>>,
    Self: CosmosChainTarget<SrcChain, DstChain, Target>,
    Target::CounterpartyChain: ChainContext<Height = Height>,
    Target::TargetChain: IbcChainContext<
        Target::CounterpartyChain,
        Message = CosmosIbcMessage,
        IbcMessage = CosmosIbcMessage,
        Event = IbcEvent,
        IbcEvent = IbcEvent,
    >,
    Target::TargetChain: MessageSenderContext,
{
    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;

    fn ibc_message_sender(&self) -> &Self::IbcMessageSender {
        &SendIbcMessagesWithUpdateClient {
            sender: SendIbcMessagesToChain,
        }
    }
}

impl<Chain> MessageSenderContext for CosmosChainHandler<Chain>
where
    Chain: ChainHandle,
{
    type MessageSender = CosmosBaseMessageSender;

    fn message_sender(&self) -> &Self::MessageSender {
        &CosmosBaseMessageSender
    }
}

#[async_trait]
impl<Chain> MessageSender<CosmosChainHandler<Chain>> for CosmosBaseMessageSender
where
    Chain: ChainHandle,
{
    async fn send_messages(
        &self,
        context: &CosmosChainHandler<Chain>,
        messages: Vec<CosmosIbcMessage>,
    ) -> Result<Vec<Vec<IbcEvent>>, Error> {
        let signer = context.handle.get_signer().map_err(Error::relayer)?;

        let raw_messages = messages
            .into_iter()
            .map(|message| message.encode_raw(&signer))
            .collect::<Result<Vec<_>, _>>()
            .map_err(Error::encode)?;

        let tracked_messages = TrackedMsgs::new_static(raw_messages, "CosmosChainHandler");

        let events = context
            .handle
            .send_messages_and_wait_commit(tracked_messages)
            .map_err(Error::relayer)?;

        // TODO: properly group IBC events by orginal order by
        // calling send_tx functions without going through ChainHandle
        let nested_events = events.into_iter().map(|event| vec![event]).collect();

        Ok(nested_events)
    }
}
