//! These functions bind the `one_for_all` trait to the `all_for_one`. Specifically,
//! this is where we 'prove' that the types that we want to implement the `all_for_one`
//! functionality implement the required trait bounds, i.e. `OfaRelayWrapper` or
//! `OfaChainWrapper`, etc.
use core::marker::PhantomData;

use crate::base::all_for_one::birelay::AfoBaseBiRelay;
use crate::base::all_for_one::chain::AfoBaseChain;
use crate::base::all_for_one::relay::AfoBaseRelay;
use crate::base::one_for_all::traits::chain::OfaIbcChain;
use crate::base::one_for_all::traits::chain::OfaIbcChainPreset;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::traits::relay::OfaRelayPreset;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::types::two_way::TwoWayRelayContext;

pub fn afo_birelay_context<RelayAToB, RelayBToA>() -> PhantomData<impl AfoBaseBiRelay>
where
    RelayAToB: OfaBaseRelay,
    RelayBToA: OfaBaseRelay<
        SrcChain = RelayAToB::DstChain,
        DstChain = RelayAToB::SrcChain,
        Error = RelayAToB::Error,
    >,
    RelayAToB::Preset: OfaRelayPreset<RelayAToB>,
    RelayBToA::Preset: OfaRelayPreset<RelayBToA>,
{
    PhantomData::<TwoWayRelayContext<OfaRelayWrapper<RelayAToB>, OfaRelayWrapper<RelayBToA>>>
}

/// Given a relay context `Relay` that implements the `OfaBaseRelay` trait, returns a type
/// that implements the `AfoBaseRelay`, meaning that this type exposes concrete APIs
/// that are used to construct custom relayer instances (i.e. relayer-cosmos).
pub fn afo_relay_context<Relay>(relay: OfaRelayWrapper<Relay>) -> impl AfoBaseRelay
where
    Relay: OfaBaseRelay,
    Relay::Preset: OfaRelayPreset<Relay>,
{
    relay
}

/// Given a chain context `Chain` that implements the `OfaIbcChain` trait, returns a type
/// that implements the `AfoBaseChain`, which is necessary for a relay context that
/// wants to relay between this IBC-enabled chain context and an IBC-enabled counterparty
/// chain context can do so.
pub fn afo_chain_context<Chain, Counterparty, Preset>(
    chain: OfaChainWrapper<Chain>,
) -> impl AfoBaseChain<OfaChainWrapper<Counterparty>>
where
    Chain: OfaIbcChain<Counterparty, Preset = Preset>,
    Counterparty: OfaIbcChain<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
    Preset: OfaIbcChainPreset<Chain, Counterparty>,
{
    chain
}
