use core::marker::PhantomData;
use ibc_relayer_framework::core::traits::contexts::chain::ChainContext;
use ibc_relayer_framework::one_for_all::traits::chain::OfaChainContext;
use ibc_relayer_framework::one_for_all::traits::components::chain::OfaIbcChainComponents;
use ibc_relayer_framework::one_for_all::traits::components::relay::OfaRelayComponents;
use ibc_relayer_framework::one_for_all::traits::relay::OfaRelayContext;

use crate::cosmos::all_for_one::chain::AfoCosmosChainContext;
use crate::cosmos::all_for_one::relay::AfoCosmosRelayContext;
use crate::cosmos::core::traits::chain::CosmosChain;
use crate::cosmos::core::traits::filter::CosmosFilter;
use crate::cosmos::core::traits::relay::CosmosRelay;
use crate::cosmos::core::types::chain::CosmosChainContext;
use crate::cosmos::core::types::relay::CosmosRelayContext;

pub fn relay_context<Relay, Filter>() -> PhantomData<impl AfoCosmosRelayContext>
where
    Relay: CosmosRelay,
    Relay::Components: OfaRelayComponents<CosmosRelayContext<Relay, Filter>>,
    Filter: CosmosFilter + Clone,
{
    PhantomData::<OfaRelayContext<CosmosRelayContext<Relay, Filter>>>
}

pub fn chain_context<Chain>() -> PhantomData<impl ChainContext>
where
    Chain: CosmosChain,
{
    PhantomData::<OfaChainContext<CosmosChainContext<Chain>>>
}

pub fn ibc_chain_context<Chain, Counterparty>(
) -> PhantomData<impl AfoCosmosChainContext<OfaChainContext<CosmosChainContext<Counterparty>>>>
where
    Chain: CosmosChain,
    Chain::Components:
        OfaIbcChainComponents<CosmosChainContext<Chain>, CosmosChainContext<Counterparty>>,
    Counterparty: CosmosChain,
{
    PhantomData::<OfaChainContext<CosmosChainContext<Chain>>>
}
