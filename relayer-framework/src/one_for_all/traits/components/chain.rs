use crate::one_for_all::traits::chain::{OfaChain, OfaChainContext, OfaIbcChain};
use crate::traits::queries::consensus_state::{CanQueryConsensusState, ConsensusStateQuerier};
use crate::traits::queries::status::{CanQueryChainStatus, ChainStatusQuerier};

pub trait OfaChainComponents<Chain>
where
    Chain: OfaChain,
{
    type ChainStatusQuerier: ChainStatusQuerier<OfaChainContext<Chain>>;
}

pub trait OfaIbcChainComponents<Chain, Counterparty>: OfaChainComponents<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConsensusStateQuerier: ConsensusStateQuerier<
        OfaChainContext<Chain>,
        OfaChainContext<Counterparty>,
    >;
}

impl<Chain, Components> CanQueryChainStatus for OfaChainContext<Chain>
where
    Chain: OfaChain<Components = Components>,
    Components: OfaChainComponents<Chain>,
{
    type ChainStatusQuerier = Components::ChainStatusQuerier;
}

impl<Chain, Counterparty, Components> CanQueryConsensusState<OfaChainContext<Counterparty>>
    for OfaChainContext<Chain>
where
    Chain: OfaIbcChain<Counterparty, Components = Components>,
    Counterparty: OfaIbcChain<Chain>,
    Components: OfaIbcChainComponents<Chain, Counterparty>,
{
    type ConsensusStateQuerier = Components::ConsensusStateQuerier;
}
