use core::marker::PhantomData;
use ibc_relayer_framework::core::traits::contexts::chain::{ChainContext, IbcChainContext};
use ibc_relayer_framework::core::traits::contexts::relay::RelayContext;
use ibc_relayer_framework::one_for_all::traits::chain::OfaChainContext;
use ibc_relayer_framework::one_for_all::traits::relay::OfaRelayContext;

use crate::cosmos::core::traits::chain::CosmosChain;
use crate::cosmos::core::traits::relay::CosmosRelay;
use crate::cosmos::core::types::chain::CosmosChainContext;
use crate::cosmos::core::types::relay::CosmosRelayContext;

pub fn relay_context<Relay>() -> PhantomData<impl RelayContext>
where
    Relay: CosmosRelay,
{
    PhantomData::<OfaRelayContext<CosmosRelayContext<Relay>>>
}

pub fn chain_context<Chain>() -> PhantomData<impl ChainContext>
where
    Chain: CosmosChain,
{
    PhantomData::<OfaChainContext<CosmosChainContext<Chain>>>
}

pub fn ibc_chain_context<Chain, Counterparty>(
) -> PhantomData<impl IbcChainContext<OfaChainContext<CosmosChainContext<Counterparty>>>>
where
    Chain: CosmosChain,
    Counterparty: CosmosChain,
{
    PhantomData::<OfaChainContext<CosmosChainContext<Chain>>>
}
