use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaChainTypes, OfaIbcChain};
use crate::extra::one_for_all::traits::runtime::OfaFullRuntime;
use crate::extra::one_for_all::traits::telemetry::OfaTelemetry;
use crate::extra::one_for_all::types::telemetry::OfaTelemetryWrapper;

pub trait OfaFullChainTypes: OfaChainTypes<Runtime = Self::FullRuntime> {
    type FullRuntime: OfaFullRuntime;
}

pub trait OfaFullChain: OfaFullChainTypes + OfaBaseChain {
    type Telemetry: OfaTelemetry;

    fn telemetry(&self) -> &OfaTelemetryWrapper<Self::Telemetry>;
}

pub trait OfaFullIbcChain<Counterparty>: OfaFullChain + OfaIbcChain<Counterparty>
where
    Counterparty: OfaIbcChain<
        Self,
        IncomingPacket = Self::OutgoingPacket,
        OutgoingPacket = Self::IncomingPacket,
    >,
{
}

impl<Chain> OfaFullChainTypes for Chain
where
    Chain: OfaChainTypes,
    Chain::Runtime: OfaFullRuntime,
{
    type FullRuntime = Chain::Runtime;
}

impl<Chain, Counterparty> OfaFullIbcChain<Counterparty> for Chain
where
    Chain: OfaFullChain + OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<
        Self,
        IncomingPacket = Self::OutgoingPacket,
        OutgoingPacket = Self::IncomingPacket,
    >,
{
}
