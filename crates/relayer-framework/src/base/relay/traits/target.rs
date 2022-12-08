use crate::base::chain::traits::types::HasIbcChainTypes;
use crate::base::chain::types::aliases::ClientId;
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::types::HasRelayTypes;

#[derive(Default)]
pub struct SourceTarget;

#[derive(Default)]
pub struct DestinationTarget;

pub trait ChainTarget<Relay: HasRelayTypes>: Async + Default + private::Sealed {
    type TargetChain: HasIbcChainTypes<Self::CounterpartyChain>;

    type CounterpartyChain: HasIbcChainTypes<Self::TargetChain>;

    fn target_chain_error(e: <Self::TargetChain as HasErrorType>::Error) -> Relay::Error;

    fn counterparty_chain_error(
        e: <Self::CounterpartyChain as HasErrorType>::Error,
    ) -> Relay::Error;

    fn target_chain(context: &Relay) -> &Self::TargetChain;

    fn counterparty_chain(context: &Relay) -> &Self::CounterpartyChain;

    fn target_client_id(context: &Relay) -> &ClientId<Self::TargetChain, Self::CounterpartyChain>;

    fn counterparty_client_id(
        context: &Relay,
    ) -> &ClientId<Self::CounterpartyChain, Self::TargetChain>;
}

impl private::Sealed for SourceTarget {}
impl private::Sealed for DestinationTarget {}

impl<Relay: HasRelayTypes> ChainTarget<Relay> for SourceTarget {
    type TargetChain = Relay::SrcChain;

    type CounterpartyChain = Relay::DstChain;

    fn target_chain_error(e: <Self::TargetChain as HasErrorType>::Error) -> Relay::Error {
        Relay::src_chain_error(e)
    }

    fn counterparty_chain_error(
        e: <Self::CounterpartyChain as HasErrorType>::Error,
    ) -> Relay::Error {
        Relay::dst_chain_error(e)
    }

    fn target_chain(context: &Relay) -> &Self::TargetChain {
        context.source_chain()
    }

    fn counterparty_chain(context: &Relay) -> &Self::CounterpartyChain {
        context.destination_chain()
    }

    fn target_client_id(context: &Relay) -> &ClientId<Self::TargetChain, Self::CounterpartyChain> {
        context.source_client_id()
    }

    fn counterparty_client_id(
        context: &Relay,
    ) -> &ClientId<Self::CounterpartyChain, Self::TargetChain> {
        context.destination_client_id()
    }
}

impl<Relay: HasRelayTypes> ChainTarget<Relay> for DestinationTarget {
    type TargetChain = Relay::DstChain;

    type CounterpartyChain = Relay::SrcChain;

    fn target_chain_error(e: <Self::TargetChain as HasErrorType>::Error) -> Relay::Error {
        Relay::dst_chain_error(e)
    }

    fn counterparty_chain_error(
        e: <Self::CounterpartyChain as HasErrorType>::Error,
    ) -> Relay::Error {
        Relay::src_chain_error(e)
    }

    fn target_chain(context: &Relay) -> &Self::TargetChain {
        context.destination_chain()
    }

    fn counterparty_chain(context: &Relay) -> &Self::CounterpartyChain {
        context.source_chain()
    }

    fn target_client_id(context: &Relay) -> &ClientId<Self::TargetChain, Self::CounterpartyChain> {
        context.destination_client_id()
    }

    fn counterparty_client_id(
        context: &Relay,
    ) -> &ClientId<Self::CounterpartyChain, Self::TargetChain> {
        context.source_client_id()
    }
}

mod private {
    pub trait Sealed {}
}
