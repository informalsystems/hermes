use crate::one_for_all::impls::chain::OfaChainContext;
use crate::one_for_all::impls::status::OfaChainStatusQuerier;
use crate::one_for_all::traits::chain::OfaChain;
use crate::traits::queries::status::{CanQueryChainStatus, ChainStatusQuerier};

pub struct OfaDefaultChainOverrides;

pub trait OfaChainOverrides<Chain>
where
    Chain: OfaChain,
{
    type ChainStatusQuerier: ChainStatusQuerier<OfaChainContext<Chain>>;
}

impl<Chain> OfaChainOverrides<Chain> for OfaDefaultChainOverrides
where
    Chain: OfaChain,
{
    type ChainStatusQuerier = OfaChainStatusQuerier;
}

impl<Chain: OfaChain> CanQueryChainStatus for OfaChainContext<Chain> {
    type ChainStatusQuerier = <Chain::Overrides as OfaChainOverrides<Chain>>::ChainStatusQuerier;
}
