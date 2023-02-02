use ibc_relayer_framework::base::relay::types::aliases::{DstChain, SrcChain};
use ibc_relayer_framework::full::all_for_one::birelay::AfoFullBiRelay;

use crate::full::all_for_one::relay::AfoCosmosFullRelay;

pub trait AfoCosmosFullBiRelay:
    AfoFullBiRelay<AfoRelayAToB = Self::CosmosRelayAToB, AfoRelayBToA = Self::CosmosRelayBToA>
{
    type CosmosRelayAToB: AfoCosmosFullRelay;

    type CosmosRelayBToA: AfoCosmosFullRelay<
        CosmosSrcChain = DstChain<Self::CosmosRelayAToB>,
        CosmosDstChain = SrcChain<Self::CosmosRelayAToB>,
    >;
}
