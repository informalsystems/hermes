use crate::one_for_all::impls::chain::OfaChainContext;
use crate::one_for_all::traits::chain::OfaChain;
use crate::traits::queries::status::{CanQueryChainStatus, ChainStatusQuerier};

pub trait OfaChainComponents<Chain>
where
    Chain: OfaChain,
{
    type ChainStatusQuerier: ChainStatusQuerier<OfaChainContext<Chain>>;
}

impl<Chain, Components> CanQueryChainStatus for OfaChainContext<Chain>
where
    Chain: OfaChain<Components = Components>,
    Components: OfaChainComponents<Chain>,
{
    type ChainStatusQuerier = Components::ChainStatusQuerier;
}

pub trait OfaChainWithComponents: OfaChain<Components = Self::ComponentsInstance> {
    type ComponentsInstance: OfaChainComponents<Self>;
}

impl<Chain> OfaChainWithComponents for Chain
where
    Chain: OfaChain,
    Chain::Components: OfaChainComponents<Chain>,
{
    type ComponentsInstance = Chain::Components;
}
