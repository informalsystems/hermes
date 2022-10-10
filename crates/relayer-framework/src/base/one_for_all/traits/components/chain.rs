use crate::base::one_for_all::traits::chain::{OfaChain, OfaChainContext, OfaIbcChain};
use crate::base::traits::queries::consensus_state::{
    ConsensusStateQuerier, HasConsensusStateQuerier,
};
use crate::base::traits::queries::status::{ChainStatusQuerier, HasChainStatusQuerier};

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

impl<Chain, Components> HasChainStatusQuerier for OfaChainContext<Chain>
where
    Chain: OfaChain<Components = Components>,
    Components: OfaChainComponents<Chain>,
{
    type ChainStatusQuerier = Components::ChainStatusQuerier;
}

impl<Chain, Counterparty, Components> HasConsensusStateQuerier<OfaChainContext<Counterparty>>
    for OfaChainContext<Chain>
where
    Chain: OfaIbcChain<Counterparty, Components = Components>,
    Counterparty: OfaIbcChain<Chain>,
    Components: OfaIbcChainComponents<Chain, Counterparty>,
{
    type ConsensusStateQuerier = Components::ConsensusStateQuerier;
}
