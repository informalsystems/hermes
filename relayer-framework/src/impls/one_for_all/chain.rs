use crate::impls::one_for_all::error::OfaErrorContext;
use crate::impls::one_for_all::message::OfaMessage;
use crate::impls::one_for_all::runtime::OfaRuntimeContext;
use crate::traits::chain_context::{ChainContext, IbcChainContext};
use crate::traits::core::ErrorContext;
use crate::traits::one_for_all::chain::OfaChain;
use crate::traits::runtime::context::RuntimeContext;

pub struct OfaChainContext<Chain: OfaChain> {
    pub chain: Chain,
    pub runtime: OfaRuntimeContext<Chain::Runtime>,
}

impl<Chain: OfaChain> ErrorContext for OfaChainContext<Chain> {
    type Error = OfaErrorContext<Chain::Error>;
}

impl<Chain: OfaChain> RuntimeContext for OfaChainContext<Chain> {
    type Runtime = OfaRuntimeContext<Chain::Runtime>;

    fn runtime(&self) -> &Self::Runtime {
        &self.runtime
    }
}

impl<Chain: OfaChain> ChainContext for OfaChainContext<Chain> {
    type Height = Chain::Height;

    type Timestamp = Chain::Timestamp;

    type Message = OfaMessage<Chain>;

    type Event = Chain::Event;
}

impl<Chain, Counterparty> IbcChainContext<Counterparty> for OfaChainContext<Chain>
where
    Chain: OfaChain,
    Counterparty: ChainContext<Height = Chain::CounterpartyHeight>,
{
    type ClientId = Chain::ClientId;

    type ConnectionId = Chain::ConnectionId;

    type ChannelId = Chain::ChannelId;

    type PortId = Chain::PortId;

    type Sequence = Chain::Sequence;

    type IbcMessage = OfaMessage<Chain>;

    type IbcEvent = Chain::Event;
}
