use core::marker::PhantomData;
use ibc_relayer_framework::base::chain::traits::context::HasChainTypes;
use ibc_relayer_framework::base::one_for_all::traits::components::chain::OfaIbcChainComponents;
use ibc_relayer_framework::base::one_for_all::traits::components::relay::OfaRelayComponents;
use ibc_relayer_framework::base::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper;

use crate::base::all_for_one::chain::AfoCosmosBaseChain;
use crate::base::all_for_one::relay::AfoCosmosBaseRelay;
use crate::base::traits::chain::CosmosChain;
use crate::base::traits::relay::CosmosRelay;
use crate::base::types::chain::CosmosChainWrapper;
use crate::base::types::relay::CosmosRelayWrapper;

pub fn relay_context<Relay>() -> PhantomData<impl AfoCosmosBaseRelay>
where
    Relay: CosmosRelay,
    Relay::Components: OfaRelayComponents<CosmosRelayWrapper<Relay>>,
{
    PhantomData::<OfaRelayWrapper<CosmosRelayWrapper<Relay>>>
}

pub fn chain_context<Chain>() -> PhantomData<impl HasChainTypes>
where
    Chain: CosmosChain,
{
    PhantomData::<OfaChainWrapper<CosmosChainWrapper<Chain>>>
}

pub fn ibc_chain_context<Chain, Counterparty>(
) -> PhantomData<impl AfoCosmosBaseChain<OfaChainWrapper<CosmosChainWrapper<Counterparty>>>>
where
    Chain: CosmosChain,
    Chain::Components:
        OfaIbcChainComponents<CosmosChainWrapper<Chain>, CosmosChainWrapper<Counterparty>>,
    Counterparty: CosmosChain,
{
    PhantomData::<OfaChainWrapper<CosmosChainWrapper<Chain>>>
}
