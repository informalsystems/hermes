use async_trait::async_trait;
use ibc::events::IbcEvent;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::tracking::TrackedMsgs;
use ibc_relayer_framework::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_framework::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_framework::traits::ibc_message_sender::IbcMessageSender;
use ibc_relayer_framework::traits::ibc_message_sender::IbcMessageSenderContext;
use ibc_relayer_framework::traits::message::Message;
use ibc_relayer_framework::traits::message_sender::{MessageSender, MessageSenderContext};
use ibc_relayer_framework::traits::target::ChainTarget;

use crate::cosmos::error::Error;
use crate::cosmos::handler::{CosmosChainHandler, CosmosRelayHandler};
use crate::cosmos::message::CosmosIbcMessage;

pub struct CosmosBaseMessageSender;

impl<SrcChain, DstChain, Target> IbcMessageSenderContext<Target>
    for CosmosRelayHandler<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
    Target: ChainTarget<CosmosRelayHandler<SrcChain, DstChain>>,
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>: IbcMessageSender<Self, Target>,
{
    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}

impl<Chain> MessageSenderContext for CosmosChainHandler<Chain>
where
    Chain: ChainHandle,
{
    type MessageSender = CosmosBaseMessageSender;
}

#[async_trait]
impl<Chain> MessageSender<CosmosChainHandler<Chain>> for CosmosBaseMessageSender
where
    Chain: ChainHandle,
{
    async fn send_messages(
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
