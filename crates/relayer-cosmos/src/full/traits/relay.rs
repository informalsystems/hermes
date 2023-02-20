use ibc_relayer::config::filter::PacketFilter;

use crate::base::traits::relay::CosmosRelay;
use crate::full::traits::chain::CosmosFullChain;
use crate::full::types::batch::CosmosBatchSender;

pub trait CosmosFullRelayTypes:
    CosmosRelay<SrcChain = Self::FullSrcChain, DstChain = Self::FullDstChain>
{
    type FullSrcChain: CosmosFullChain<Preset = Self::Preset>;
    type FullDstChain: CosmosFullChain<Preset = Self::Preset>;
}

pub trait CosmosFullRelay: CosmosFullRelayTypes {
    fn packet_filter(&self) -> &PacketFilter;

    fn src_chain_message_batch_sender(&self) -> &CosmosBatchSender;

    fn dst_chain_message_batch_sender(&self) -> &CosmosBatchSender;
}

impl<Relay> CosmosFullRelayTypes for Relay
where
    Relay: CosmosRelay,
    Relay::SrcChain: CosmosFullChain,
    Relay::DstChain: CosmosFullChain,
{
    type FullSrcChain = Relay::SrcChain;
    type FullDstChain = Relay::DstChain;
}
