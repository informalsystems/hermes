use crate::base::one_for_all::traits::chain::OfaIbcChain;
use crate::base::one_for_all::traits::chain::{OfaChainPreset, OfaIbcChainPreset};
use crate::base::one_for_all::traits::relay::OfaRelayPreset;
use crate::full::one_for_all::presets::full as preset;
use crate::full::one_for_all::presets::full::FullPreset;
use crate::full::one_for_all::traits::chain::OfaFullChain;
use crate::full::one_for_all::traits::relay::OfaFullRelay;

impl<Chain> OfaChainPreset<Chain> for FullPreset
where
    Chain: OfaFullChain,
{
    type ChainStatusQuerier = preset::ChainStatusQuerier;
}

impl<Chain, Counterparty> OfaIbcChainPreset<Chain, Counterparty> for FullPreset
where
    Chain: OfaFullChain,
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConsensusStateQuerier = preset::ConsensusStateQuerier;
}

impl<Relay> OfaRelayPreset<Relay> for FullPreset
where
    Relay: OfaFullRelay<Preset = FullPreset>,
    Relay::SrcChain: OfaFullChain<Error = Relay::Error>,
    Relay::DstChain: OfaFullChain<Error = Relay::Error>,
{
    type PacketRelayer = preset::PacketRelayer;

    type IbcMessageSender = preset::IbcMessageSender;
}
