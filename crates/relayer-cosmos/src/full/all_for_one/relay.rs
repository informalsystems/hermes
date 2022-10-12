use ibc_relayer_framework::full::all_for_one::relay::AfoFullRelay;
use ibc_relayer_types::core::ics04_channel::packet::Packet;

use crate::full::all_for_one::chain::AfoCosmosFullChain;

pub trait AfoCosmosFullRelay:
    AfoFullRelay<
    AfoSrcFullChain = Self::SrcCosmosFullChain,
    AfoDstFullChain = Self::DstCosmosFullChain,
    Packet = Packet,
>
{
    type SrcCosmosFullChain: AfoCosmosFullChain<Self::DstCosmosFullChain>;

    type DstCosmosFullChain: AfoCosmosFullChain<Self::SrcCosmosFullChain>;
}

impl<Relay, SrcChain, DstChain> AfoCosmosFullRelay for Relay
where
    Relay: AfoFullRelay<AfoSrcFullChain = SrcChain, AfoDstFullChain = DstChain, Packet = Packet>,
    SrcChain: AfoCosmosFullChain<DstChain>,
    DstChain: AfoCosmosFullChain<SrcChain>,
{
    type SrcCosmosFullChain = SrcChain;
    type DstCosmosFullChain = DstChain;
}
