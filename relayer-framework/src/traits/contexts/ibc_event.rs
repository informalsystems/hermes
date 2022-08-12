use crate::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::traits::core::Async;

pub trait IbcEventContext<Counterparty>: IbcChainContext<Counterparty>
where
    Counterparty: ChainContext,
{
    type WriteAcknowledgementEvent: Async + TryFrom<Self::IbcEvent>;
}
