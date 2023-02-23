use crate::chain::traits::types::chain::HasChainTypes;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::sync::Async;

pub trait HasConsensusStateType<Counterparty>: HasIbcChainTypes<Counterparty>
where
    Counterparty: HasChainTypes,
{
    type ConsensusState: Async;
}
