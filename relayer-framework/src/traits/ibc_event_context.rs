use crate::traits::chain_context::{ChainContext, IbcChainContext};
use crate::traits::core::Async;

pub trait IbcEventContext<Counterparty>: IbcChainContext<Counterparty>
where
    Counterparty: ChainContext,
{
    type WriteAcknowledgementEvent: Async + TryFrom<Self::IbcEvent> + Into<Self::IbcEvent>;
}
