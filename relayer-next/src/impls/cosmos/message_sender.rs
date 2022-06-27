use async_trait::async_trait;
use ibc::events::IbcEvent;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::tracking::TrackedMsgs;

use crate::impls::cosmos::chain_types::CosmosChainTypes;
use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::handler::CosmosRelayHandler;
use crate::impls::cosmos::message::CosmosIbcMessage;
use crate::impls::cosmos::relay_types::CosmosRelayTypes;
use crate::impls::cosmos::target::CosmosChainTarget;
use crate::impls::message_senders::update_client::MessageSenderWithUpdateClient;
use crate::traits::message::Message;
use crate::traits::message_sender::{IbcMessageSender, MessageSenderContext};
use crate::traits::target::ChainTarget;

pub struct CosmosBaseMessageSender;

impl<SrcChain, DstChain, Target> MessageSenderContext<Target>
    for CosmosRelayHandler<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
    Target: ChainTarget<
        CosmosRelayTypes,
        TargetChain = CosmosChainTypes,
        CounterpartyChain = CosmosChainTypes,
    >,
    Self: CosmosChainTarget<Target>,
{
    type Sender = MessageSenderWithUpdateClient<CosmosBaseMessageSender>;

    fn message_sender(&self) -> &Self::Sender {
        &MessageSenderWithUpdateClient {
            sender: CosmosBaseMessageSender,
        }
    }
}

#[async_trait]
impl<SrcChain, DstChain, Target> IbcMessageSender<CosmosRelayHandler<SrcChain, DstChain>, Target>
    for CosmosBaseMessageSender
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
    Target: ChainTarget<
        CosmosRelayTypes,
        TargetChain = CosmosChainTypes,
        CounterpartyChain = CosmosChainTypes,
    >,
    CosmosRelayHandler<SrcChain, DstChain>: CosmosChainTarget<Target>,
{
    async fn send_messages(
        &self,
        context: &CosmosRelayHandler<SrcChain, DstChain>,
        messages: Vec<CosmosIbcMessage>,
    ) -> Result<Vec<Vec<IbcEvent>>, Error> {
        let signer = context
            .target_handle()
            .get_signer()
            .map_err(Error::relayer)?;

        let raw_messages = messages
            .into_iter()
            .map(|message| message.encode_raw(&signer))
            .collect::<Result<Vec<_>, _>>()
            .map_err(Error::encode)?;

        let tracked_messages = TrackedMsgs::new_static(raw_messages, "CosmosChainTypes");

        let events = context
            .target_handle()
            .send_messages_and_wait_commit(tracked_messages)
            .map_err(Error::relayer)?;

        // TODO: properly group IBC events by orginal order by
        // calling send_tx functions without going through ChainHandle
        let nested_events = events.into_iter().map(|event| vec![event]).collect();

        Ok(nested_events)
    }
}
