use crate::base::chain::traits::types::chain::HasChainTypes;
use crate::base::chain::traits::types::ibc::HasIbcChainTypes;
use crate::base::core::traits::sync::Async;

pub trait HasConsensusStateType<Counterparty>: HasIbcChainTypes<Counterparty>
where
    Counterparty: HasChainTypes,
{
    type ConsensusState: Async;
}
