use crate::base::chain::traits::context::{HasChainTypes, HasIbcChainTypes};
use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::core::traits::error::HasError;
use crate::base::core::traits::runtime::HasRuntime;
use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaIbcChain};
use crate::base::one_for_all::traits::runtime::OfaRuntimeContext;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

impl<Chain: OfaBaseChain> HasError for OfaChainWrapper<Chain> {
    type Error = Chain::Error;
}

impl<Chain: OfaBaseChain> HasRuntime for OfaChainWrapper<Chain> {
    type Runtime = OfaRuntimeContext<Chain::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.chain.runtime()
    }
}

impl<Chain: OfaBaseChain> HasChainTypes for OfaChainWrapper<Chain> {
    type Height = Chain::Height;

    type Timestamp = Chain::Timestamp;

    type Message = Chain::Message;

    type Signer = Chain::Signer;

    type Event = Chain::Event;

    fn estimate_message_len(message: &Self::Message) -> Result<usize, Self::Error> {
        Chain::estimate_message_len(message)
    }
}

impl<Chain, Counterparty> HasIbcChainTypes<OfaChainWrapper<Counterparty>> for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaBaseChain,
{
    type ClientId = Chain::ClientId;

    type ConnectionId = Chain::ConnectionId;

    type ChannelId = Chain::ChannelId;

    type PortId = Chain::PortId;

    type Sequence = Chain::Sequence;

    fn counterparty_message_height(message: &Self::Message) -> Option<Counterparty::Height> {
        Chain::counterparty_message_height(message)
    }
}

impl<Chain, Counterparty> HasIbcEvents<OfaChainWrapper<Counterparty>> for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaBaseChain,
{
    type WriteAcknowledgementEvent = Chain::WriteAcknowledgementEvent;

    fn try_extract_write_acknowledgement_event(
        event: Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent> {
        Chain::try_extract_write_acknowledgement_event(event)
    }
}
