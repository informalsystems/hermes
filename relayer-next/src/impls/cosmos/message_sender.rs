use async_trait::async_trait;
use eyre::eyre;
use ibc::events::IbcEvent;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::tracking::TrackedMsgs;

use crate::impls::cosmos::chain_types::CosmosChainTypes;
use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::handler::CosmosRelayHandler;
use crate::impls::cosmos::message::CosmosIbcMessage;
use crate::impls::cosmos::relay_types::CosmosRelayTypes;
use crate::impls::cosmos::target::CosmosChainTarget;
use crate::traits::message::Message;
use crate::traits::message_sender::IbcMessageSender;
use crate::traits::target::ChainTarget;

#[async_trait]
impl<SrcChain, DstChain, Target> IbcMessageSender<CosmosRelayTypes, Target>
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
    async fn send_message(&self, message: CosmosIbcMessage) -> Result<Vec<IbcEvent>, Error> {
        let signer = self.target_handle().get_signer().map_err(Error::relayer)?;

        let raw_message = message.encode_raw(&signer).map_err(Error::encode)?;

        let tracked_messages = TrackedMsgs::new_static(vec![raw_message], "CosmosChainTypes");

        let events = self
            .target_handle()
            .send_messages_and_wait_commit(tracked_messages)
            .map_err(Error::relayer)?;

        Ok(events)
    }

    async fn send_messages(
        &self,
        messages: Vec<CosmosIbcMessage>,
    ) -> Result<Vec<Vec<IbcEvent>>, Error> {
        let signer = self.target_handle().get_signer().map_err(Error::relayer)?;

        let raw_messages = messages
            .into_iter()
            .map(|message| message.encode_raw(&signer))
            .collect::<Result<Vec<_>, _>>()
            .map_err(Error::encode)?;

        let tracked_messages = TrackedMsgs::new_static(raw_messages, "CosmosChainTypes");

        let events = self
            .target_handle()
            .send_messages_and_wait_commit(tracked_messages)
            .map_err(Error::relayer)?;

        // TODO: properly group IBC events by orginal order by
        // calling send_tx functions without going through ChainHandle
        let nested_events = events.into_iter().map(|event| vec![event]).collect();

        Ok(nested_events)
    }

    async fn send_messages_fixed<const COUNT: usize>(
        &self,
        messages: [CosmosIbcMessage; COUNT],
    ) -> Result<[Vec<IbcEvent>; COUNT], Error> {
        let events = self
            .send_messages(messages.into())
            .await?
            .try_into()
            .map_err(|e: Vec<_>| {
                Error::generic(eyre!(
                    "mismatch size for events returned. expected: {}, got: {}",
                    COUNT,
                    e.len()
                ))
            })?;

        Ok(events)
    }
}
