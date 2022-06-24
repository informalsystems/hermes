use async_trait::async_trait;
use ibc::events::IbcEvent;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::tracking::TrackedMsgs;

use crate::impls::cosmos::chain_context::CosmosChainContext;
use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::message::CosmosIbcMessage;
use crate::traits::message::Message;
use crate::traits::message_sender::IbcMessageSender;

#[async_trait]
impl<Chain, Counterparty> IbcMessageSender<CosmosChainContext<Counterparty>>
    for CosmosChainContext<Chain>
where
    Chain: ChainHandle,
    Counterparty: ChainHandle,
{
    async fn send_message(&self, message: CosmosIbcMessage) -> Result<Vec<IbcEvent>, Self::Error> {
        let signer = self.handle.get_signer().map_err(Error::relayer)?;

        let raw_message = message.encode_raw(&signer).map_err(Error::encode)?;

        let tracked_messages = TrackedMsgs::new_static(vec![raw_message], "CosmosChainContext");

        let events = self
            .handle
            .send_messages_and_wait_commit(tracked_messages)
            .map_err(Error::relayer)?;

        Ok(events)
    }

    async fn send_messages(
        &self,
        messages: Vec<CosmosIbcMessage>,
    ) -> Result<Vec<Vec<IbcEvent>>, Self::Error> {
        let signer = self.handle.get_signer().map_err(Error::relayer)?;

        let raw_messages = messages
            .into_iter()
            .map(|message| message.encode_raw(&signer))
            .collect::<Result<Vec<_>, _>>()
            .map_err(Error::encode)?;

        let tracked_messages = TrackedMsgs::new_static(raw_messages, "CosmosChainContext");

        let events = self
            .handle
            .send_messages_and_wait_commit(tracked_messages)
            .map_err(Error::relayer)?;

        // TODO: properly group IBC events by orginal order by
        // calling send_tx functions without going through ChainHandle
        let nested_events = events.into_iter().map(|event| vec![event]).collect();

        Ok(nested_events)
    }
}
