use core::marker::PhantomData;
use ibc_relayer_framework::base::all_for_one::birelay::AfoBaseBiRelay;
use ibc_relayer_framework::base::chain::traits::types::chain::HasChainTypes;
use ibc_relayer_framework::base::one_for_all::traits::chain::OfaIbcChainPreset;
use ibc_relayer_framework::base::one_for_all::traits::relay::OfaRelayPreset;
use ibc_relayer_framework::base::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_framework::base::one_for_all::types::relay::OfaRelayWrapper;
use ibc_relayer_framework::base::relay::types::two_way::TwoWayRelayContext;
use ibc_relayer_framework::full::relay::impls::auto_relayers::parallel_two_way::ParallelTwoWayAutoRelay;

use crate::base::all_for_one::chain::AfoCosmosBaseChain;
use crate::base::all_for_one::relay::AfoCosmosBaseRelay;
use crate::base::traits::chain::CosmosChain;
use crate::base::traits::relay::CosmosRelay;
use crate::base::types::chain::CosmosChainWrapper;
use crate::base::types::relay::CosmosRelayWrapper;

pub fn birelay_context<RelayAToB, RelayBToA>() -> PhantomData<impl AfoBaseBiRelay>
where
    RelayAToB: CosmosRelay,
    RelayBToA: CosmosRelay<SrcChain = RelayAToB::DstChain, DstChain = RelayAToB::SrcChain>,
    RelayAToB::Preset: OfaRelayPreset<CosmosRelayWrapper<RelayAToB>>,
    RelayBToA::Preset: OfaRelayPreset<CosmosRelayWrapper<RelayBToA>>,
{
    PhantomData::<
        TwoWayRelayContext<
            ParallelTwoWayAutoRelay,
            OfaRelayWrapper<CosmosRelayWrapper<RelayAToB>>,
            OfaRelayWrapper<CosmosRelayWrapper<RelayBToA>>,
        >,
    >
}

pub fn relay_context<Relay>() -> PhantomData<impl AfoCosmosBaseRelay>
where
    Relay: CosmosRelay,
    Relay::Preset: OfaRelayPreset<CosmosRelayWrapper<Relay>>,
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
    Chain::Preset: OfaIbcChainPreset<CosmosChainWrapper<Chain>, CosmosChainWrapper<Counterparty>>,
    Counterparty: CosmosChain,
{
    PhantomData::<OfaChainWrapper<CosmosChainWrapper<Chain>>>
}
