use crate::base::chain::traits::queries::consensus_state::{
    ConsensusStateQuerier, HasConsensusStateQuerier,
};
use crate::base::chain::traits::queries::status::{ChainStatusQuerier, HasChainStatusQuerier};
use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaIbcChain};
use crate::base::one_for_all::types::chain::OfaChainWrapper;

pub trait OfaBaseChainComponents<Chain>
where
    Chain: OfaBaseChain,
{
    type ChainStatusQuerier: ChainStatusQuerier<OfaChainWrapper<Chain>>;
}

pub trait OfaIbcChainComponents<Chain, Counterparty>: OfaBaseChainComponents<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConsensusStateQuerier: ConsensusStateQuerier<
        OfaChainWrapper<Chain>,
        OfaChainWrapper<Counterparty>,
    >;
}

impl<Chain, Components> HasChainStatusQuerier for OfaChainWrapper<Chain>
where
    Chain: OfaBaseChain<Components = Components>,
    Components: OfaBaseChainComponents<Chain>,
{
    type ChainStatusQuerier = Components::ChainStatusQuerier;
}

impl<Chain, Counterparty, Components> HasConsensusStateQuerier<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty, Components = Components>,
    Counterparty: OfaIbcChain<Chain>,
    Components: OfaIbcChainComponents<Chain, Counterparty>,
{
    type ConsensusStateQuerier = Components::ConsensusStateQuerier;
}
