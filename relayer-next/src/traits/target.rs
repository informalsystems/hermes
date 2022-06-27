use crate::traits::chain_types::IbcChainContext;
use crate::traits::core::Async;
use crate::traits::relay_types::RelayContext;

pub struct SourceTarget;

pub struct DestinationTarget;

pub trait ChainTarget<Relay: RelayContext>: Async + private::Sealed {
    type TargetChain: IbcChainContext<Self::CounterpartyChain, Error = Relay::Error>;

    type CounterpartyChain: IbcChainContext<Self::TargetChain, Error = Relay::Error>;
}

impl private::Sealed for SourceTarget {}
impl private::Sealed for DestinationTarget {}

impl<Relay: RelayContext> ChainTarget<Relay> for SourceTarget {
    type TargetChain = Relay::SrcChain;
    type CounterpartyChain = Relay::DstChain;
}

impl<Relay: RelayContext> ChainTarget<Relay> for DestinationTarget {
    type TargetChain = Relay::DstChain;
    type CounterpartyChain = Relay::SrcChain;
}

mod private {
    pub trait Sealed {}
}
