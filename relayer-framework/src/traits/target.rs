use crate::traits::chain_context::IbcChainContext;
use crate::traits::core::Async;
use crate::traits::relay_context::RelayContext;

pub struct SourceTarget;

pub struct DestinationTarget;

pub trait ChainTarget<Relay: RelayContext>: Async + private::Sealed {
    type TargetChain: IbcChainContext<Self::CounterpartyChain, Error = Relay::Error>;

    type CounterpartyChain: IbcChainContext<Self::TargetChain, Error = Relay::Error>;

    fn target_chain(context: &Relay) -> &Self::TargetChain;

    fn counterparty_chain(context: &Relay) -> &Self::CounterpartyChain;
}

impl private::Sealed for SourceTarget {}
impl private::Sealed for DestinationTarget {}

impl<Relay: RelayContext> ChainTarget<Relay> for SourceTarget {
    type TargetChain = Relay::SrcChain;
    type CounterpartyChain = Relay::DstChain;

    fn target_chain(context: &Relay) -> &Self::TargetChain {
        context.source_chain()
    }

    fn counterparty_chain(context: &Relay) -> &Self::CounterpartyChain {
        context.destination_chain()
    }
}

impl<Relay: RelayContext> ChainTarget<Relay> for DestinationTarget {
    type TargetChain = Relay::DstChain;
    type CounterpartyChain = Relay::SrcChain;

    fn target_chain(context: &Relay) -> &Self::TargetChain {
        context.destination_chain()
    }

    fn counterparty_chain(context: &Relay) -> &Self::CounterpartyChain {
        context.source_chain()
    }
}

mod private {
    pub trait Sealed {}
}
