use ibc_relayer_all_in_one::one_for_all::traits::birelay::{OfaBiRelay, OfaBiRelayPreset};
use ibc_relayer_all_in_one::one_for_all::traits::chain::OfaIbcChain;
use ibc_relayer_all_in_one::one_for_all::traits::chain::{OfaChainPreset, OfaIbcChainPreset};
use ibc_relayer_all_in_one::one_for_all::traits::relay::OfaRelayPreset;

use crate::one_for_all::presets::full::{self as preset, FullPreset};
use crate::one_for_all::traits::chain::OfaFullChain;
use crate::one_for_all::traits::relay::OfaFullRelay;

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
    Counterparty: OfaIbcChain<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
{
    type ConsensusStateQuerier = preset::ConsensusStateQuerier;
}

impl<Relay> OfaRelayPreset<Relay> for FullPreset
where
    Relay: OfaFullRelay<Preset = FullPreset>,
    Relay::SrcChain: OfaFullChain,
    Relay::DstChain: OfaFullChain,
{
    type AutoRelayer = preset::AutoRelayer;

    type PacketRelayer = preset::PacketRelayer;

    type PacketFilter = preset::PacketFilter;

    type IbcMessageSender = preset::IbcMessageSender;
}

impl<BiRelay, RelayAToB, RelayBToA> OfaBiRelayPreset<BiRelay> for FullPreset
where
    BiRelay: OfaBiRelay<Preset = FullPreset, RelayAToB = RelayAToB, RelayBToA = RelayBToA>,
    RelayAToB: OfaFullRelay<Preset = FullPreset>,
    RelayBToA: OfaFullRelay<Preset = FullPreset>,
{
    type TwoWayAutoRelayer = preset::TwoWayAutoRelayer;
}
