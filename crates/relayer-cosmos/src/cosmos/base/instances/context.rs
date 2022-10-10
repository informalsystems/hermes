use core::marker::PhantomData;
use ibc_relayer_framework::base::one_for_all::traits::chain::OfaChainWrapper;
use ibc_relayer_framework::base::one_for_all::traits::components::chain::OfaIbcChainComponents;
use ibc_relayer_framework::base::one_for_all::traits::components::relay::OfaRelayComponents;
use ibc_relayer_framework::base::one_for_all::traits::relay::OfaRelayWrapper;
use ibc_relayer_framework::base::traits::contexts::chain::ChainContext;

use crate::cosmos::base::all_for_one::chain::AfoCosmosChainContext;
use crate::cosmos::base::all_for_one::relay::AfoCosmosRelayContext;
use crate::cosmos::base::traits::chain::CosmosChain;
use crate::cosmos::base::traits::filter::CosmosFilter;
use crate::cosmos::base::traits::relay::CosmosRelay;
use crate::cosmos::base::types::chain::CosmosChainWrapper;
use crate::cosmos::base::types::relay::CosmosRelayWrapper;

pub fn relay_context<Relay, Filter>() -> PhantomData<impl AfoCosmosRelayContext>
where
    Relay: CosmosRelay,
    Relay::Components: OfaRelayComponents<CosmosRelayWrapper<Relay, Filter>>,
    Filter: CosmosFilter + Clone,
{
    PhantomData::<OfaRelayWrapper<CosmosRelayWrapper<Relay, Filter>>>
}

pub fn chain_context<Chain>() -> PhantomData<impl ChainContext>
where
    Chain: CosmosChain,
{
    PhantomData::<OfaChainWrapper<CosmosChainWrapper<Chain>>>
}

pub fn ibc_chain_context<Chain, Counterparty>(
) -> PhantomData<impl AfoCosmosChainContext<OfaChainWrapper<CosmosChainWrapper<Counterparty>>>>
where
    Chain: CosmosChain,
    Chain::Components:
        OfaIbcChainComponents<CosmosChainWrapper<Chain>, CosmosChainWrapper<Counterparty>>,
    Counterparty: CosmosChain,
{
    PhantomData::<OfaChainWrapper<CosmosChainWrapper<Chain>>>
}
