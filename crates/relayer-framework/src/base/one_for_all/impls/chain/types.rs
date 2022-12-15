use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::traits::types::{
    HasChainTypes, HasEventType, HasIbcChainTypes, HasMessageType,
};
use crate::base::core::traits::error::HasErrorType;
use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaIbcChain};
use crate::base::one_for_all::traits::runtime::OfaRuntimeWrapper;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::std_prelude::*;

impl<Chain: OfaBaseChain> HasErrorType for OfaChainWrapper<Chain> {
    type Error = Chain::Error;
}

impl<Chain: OfaBaseChain> HasRuntime for OfaChainWrapper<Chain> {
    type Runtime = OfaRuntimeWrapper<Chain::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        self.chain.runtime()
    }

    fn runtime_error(e: <Self::Runtime as HasErrorType>::Error) -> Chain::Error {
        Chain::runtime_error(e)
    }
}

impl<Chain: OfaBaseChain> HasMessageType for OfaChainWrapper<Chain> {
    type Message = Chain::Message;

    fn estimate_message_len(message: &Self::Message) -> Result<usize, Self::Error> {
        Chain::estimate_message_len(message)
    }
}

impl<Chain: OfaBaseChain> HasEventType for OfaChainWrapper<Chain> {
    type Event = Chain::Event;
}

impl<Chain: OfaBaseChain> HasChainTypes for OfaChainWrapper<Chain> {
    type Height = Chain::Height;

    type Timestamp = Chain::Timestamp;
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
