use ibc_relayer_all_in_one::all_for_one::relay::AfoRelay;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;
use ibc_relayer_types::core::ics04_channel::packet::Packet;

use crate::all_for_one::chain::AfoCosmosChain;

pub trait AfoCosmosRelay:
    AfoRelay<
    AfoSrcChain = Self::CosmosSrcChain,
    AfoDstChain = Self::CosmosDstChain,
    Packet = Packet,
    AfoRuntime = TokioRuntimeContext,
>
{
    type CosmosSrcChain: AfoCosmosChain<Self::CosmosDstChain>;

    type CosmosDstChain: AfoCosmosChain<Self::CosmosSrcChain>;
}

impl<Relay, SrcChain, DstChain> AfoCosmosRelay for Relay
where
    Relay: AfoRelay<
        AfoSrcChain = SrcChain,
        AfoDstChain = DstChain,
        Packet = Packet,
        AfoRuntime = TokioRuntimeContext,
    >,
    SrcChain: AfoCosmosChain<DstChain>,
    DstChain: AfoCosmosChain<SrcChain>,
{
    type CosmosSrcChain = SrcChain;
    type CosmosDstChain = DstChain;
}
