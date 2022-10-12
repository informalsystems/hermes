use ibc_relayer_framework::base::all_for_one::relay::AfoBaseRelay;
use ibc_relayer_types::core::ics04_channel::packet::Packet;

use crate::base::all_for_one::chain::AfoCosmosBaseChain;

pub trait AfoCosmosBaseRelay:
    AfoBaseRelay<
    AfoSrcChain = Self::SrcCosmosChain,
    AfoDstChain = Self::DstCosmosChain,
    Packet = Packet,
>
{
    type SrcCosmosChain: AfoCosmosBaseChain<Self::DstCosmosChain>;

    type DstCosmosChain: AfoCosmosBaseChain<Self::SrcCosmosChain>;
}

impl<Relay, SrcChain, DstChain> AfoCosmosBaseRelay for Relay
where
    Relay: AfoBaseRelay<AfoSrcChain = SrcChain, AfoDstChain = DstChain, Packet = Packet>,
    SrcChain: AfoCosmosBaseChain<DstChain>,
    DstChain: AfoCosmosBaseChain<SrcChain>,
{
    type SrcCosmosChain = SrcChain;
    type DstCosmosChain = DstChain;
}
