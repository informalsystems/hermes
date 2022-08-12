use crate::traits::contexts::chain::{ChainContext, IbcChainContext};
use crate::traits::core::Async;

pub trait HasIbcEvents<Counterparty>: IbcChainContext<Counterparty>
where
    Counterparty: ChainContext,
{
    type WriteAcknowledgementEvent: Async + TryFrom<Self::IbcEvent>;
}
