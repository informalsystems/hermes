use crate::one_for_all::impls::status::OfaChainStatusQuerier;
use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::traits::components::chain::OfaChainComponents;

pub struct DefaultComponents;

impl<Chain> OfaChainComponents<Chain> for DefaultComponents
where
    Chain: OfaChain,
{
    type ChainStatusQuerier = OfaChainStatusQuerier;
}
