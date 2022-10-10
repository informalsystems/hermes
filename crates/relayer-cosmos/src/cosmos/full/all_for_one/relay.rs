use ibc_relayer_framework::base::one_for_all::traits::error::OfaErrorContext;
use ibc_relayer_framework::full::all_for_one::relay::AfoFullRelayContext;
use ibc_relayer_types::core::ics04_channel::packet::Packet;

use crate::cosmos::base::error::Error;
use crate::cosmos::full::all_for_one::chain::AfoCosmosFullChainContext;

pub trait AfoCosmosFullRelayContext:
    AfoFullRelayContext<
    AfoError = OfaErrorContext<Error>,
    AfoSrcFullChain = Self::SrcCosmosFullChain,
    AfoDstFullChain = Self::DstCosmosFullChain,
    Packet = Packet,
>
{
    type SrcCosmosFullChain: AfoCosmosFullChainContext<Self::DstCosmosFullChain>;

    type DstCosmosFullChain: AfoCosmosFullChainContext<Self::SrcCosmosFullChain>;
}

impl<Relay, SrcChain, DstChain> AfoCosmosFullRelayContext for Relay
where
    Relay: AfoFullRelayContext<
        AfoError = OfaErrorContext<Error>,
        AfoSrcFullChain = SrcChain,
        AfoDstFullChain = DstChain,
        Packet = Packet,
    >,
    SrcChain: AfoCosmosFullChainContext<DstChain>,
    DstChain: AfoCosmosFullChainContext<SrcChain>,
{
    type SrcCosmosFullChain = SrcChain;
    type DstCosmosFullChain = DstChain;
}
