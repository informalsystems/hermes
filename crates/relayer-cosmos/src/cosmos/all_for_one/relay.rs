use ibc_relayer_framework::base::all_for_one::traits::relay::AfoRelayContext;
use ibc_relayer_framework::base::one_for_all::traits::error::OfaErrorContext;
use ibc_relayer_types::core::ics04_channel::packet::Packet;

use crate::cosmos::all_for_one::chain::AfoCosmosChainContext;
use crate::cosmos::core::error::Error;

pub trait AfoCosmosRelayContext:
    AfoRelayContext<
    AfoError = OfaErrorContext<Error>,
    AfoSrcChain = Self::CosmosSrcChain,
    AfoDstChain = Self::CosmosDstChain,
    Packet = Packet,
>
{
    type CosmosSrcChain: AfoCosmosChainContext<Self::CosmosDstChain>;

    type CosmosDstChain: AfoCosmosChainContext<Self::CosmosSrcChain>;
}

impl<Relay, SrcChain, DstChain> AfoCosmosRelayContext for Relay
where
    Relay: AfoRelayContext<
        AfoError = OfaErrorContext<Error>,
        AfoSrcChain = SrcChain,
        AfoDstChain = DstChain,
        Packet = Packet,
    >,
    SrcChain: AfoCosmosChainContext<DstChain>,
    DstChain: AfoCosmosChainContext<SrcChain>,
{
    type CosmosSrcChain = SrcChain;
    type CosmosDstChain = DstChain;
}
