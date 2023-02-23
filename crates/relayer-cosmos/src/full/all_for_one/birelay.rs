use ibc_relayer_all_in_one::extra::all_for_one::birelay::AfoFullBiRelay;
use ibc_relayer_components::relay::types::aliases::{DstChain, SrcChain};

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

impl<BiRelay, RelayAToB, RelayBToA> AfoCosmosFullBiRelay for BiRelay
where
    BiRelay: AfoFullBiRelay<AfoRelayAToB = RelayAToB, AfoRelayBToA = RelayBToA>,
    RelayAToB: AfoCosmosFullRelay,
    RelayBToA: AfoCosmosFullRelay<
        CosmosSrcChain = RelayAToB::DstChain,
        CosmosDstChain = RelayAToB::SrcChain,
    >,
{
    type CosmosRelayAToB = RelayAToB;

    type CosmosRelayBToA = RelayBToA;
}
