use ibc_relayer_framework::base::all_for_one::relay::AfoBaseRelay;

use crate::base::all_for_one::chain::AfoCosmosBaseChain;

pub trait AfoCosmosBaseRelay:
    AfoBaseRelay<AfoSrcChain = Self::CosmosSrcChain, AfoDstChain = Self::CosmosDstChain>
{
    type CosmosSrcChain: AfoCosmosBaseChain<Self::CosmosDstChain>;

    type CosmosDstChain: AfoCosmosBaseChain<Self::CosmosSrcChain>;
}

impl<Relay, SrcChain, DstChain> AfoCosmosBaseRelay for Relay
where
    Relay: AfoBaseRelay<AfoSrcChain = SrcChain, AfoDstChain = DstChain>,
    SrcChain: AfoCosmosBaseChain<DstChain>,
    DstChain: AfoCosmosBaseChain<SrcChain>,
{
    type CosmosSrcChain = SrcChain;
    type CosmosDstChain = DstChain;
}
