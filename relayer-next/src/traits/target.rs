use crate::traits::chain_types::IbcChainTypes;
use crate::traits::core::CoreTraits;
use crate::traits::relay_types::RelayTypes;

pub struct SourceTarget;

pub struct DestinationTarget;

pub trait ChainTarget<Relay: RelayTypes>: CoreTraits + private::Sealed {
    type TargetChain: IbcChainTypes<Self::CounterpartyChain, Error = Relay::Error>;

    type CounterpartyChain: IbcChainTypes<Self::TargetChain, Error = Relay::Error>;
}

impl private::Sealed for SourceTarget {}
impl private::Sealed for DestinationTarget {}

impl<Relay: RelayTypes> ChainTarget<Relay> for SourceTarget {
    type TargetChain = Relay::SrcChain;
    type CounterpartyChain = Relay::DstChain;
}

impl<Relay: RelayTypes> ChainTarget<Relay> for DestinationTarget {
    type TargetChain = Relay::DstChain;
    type CounterpartyChain = Relay::SrcChain;
}

mod private {
    pub trait Sealed {}
}
