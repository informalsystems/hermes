use async_trait::async_trait;
use ibc_relayer::chain::cosmos::tx::simple_send_tx;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_framework::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_framework::traits::ibc_message_sender::{
    IbcMessageSender, IbcMessageSenderContext,
};
use ibc_relayer_framework::traits::message::Message;
use ibc_relayer_framework::traits::message_sender::{MessageSender, MessageSenderContext};
use ibc_relayer_framework::traits::target::ChainTarget;
use tendermint::abci::responses::Event;

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::context::relay::CosmosRelayContext;
use crate::cosmos::error::Error;
use crate::cosmos::message::CosmosIbcMessage;

pub struct CosmosBaseMessageSender;

impl<SrcChain, DstChain, Target> IbcMessageSenderContext<Target>
    for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
    Target: ChainTarget<CosmosRelayContext<SrcChain, DstChain>>,
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>: IbcMessageSender<Self, Target>,
{
    type IbcMessageSender = SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>;
}

impl<Chain> MessageSenderContext for CosmosChainContext<Chain>
where
    Chain: ChainHandle,
{
    type MessageSender = CosmosBaseMessageSender;
}

#[async_trait]
impl<Chain> MessageSender<CosmosChainContext<Chain>> for CosmosBaseMessageSender
where
    Chain: ChainHandle,
{
    async fn send_messages(
        context: &CosmosChainContext<Chain>,
        messages: Vec<CosmosIbcMessage>,
    ) -> Result<Vec<Vec<Event>>, Error> {
        let signer = &context.signer;

        let raw_messages = messages
            .into_iter()
            .map(|message| message.encode_raw(signer))
            .collect::<Result<Vec<_>, _>>()
            .map_err(Error::encode)?;

        let events = simple_send_tx(&context.tx_config, &context.key_entry, raw_messages)
            .await
            .map_err(Error::relayer)?;

        Ok(events)
    }
}
