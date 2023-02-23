use async_trait::async_trait;
use ibc_relayer_all_in_one::one_for_all::traits::chain::OfaIbcChain;
use ibc_relayer_all_in_one::one_for_all::traits::relay::{OfaBaseRelay, OfaRelayTypes};

use crate::one_for_all::traits::chain::{OfaFullChain, OfaFullIbcChain};
use crate::one_for_all::traits::runtime::OfaFullRuntime;
use crate::one_for_all::types::batch::aliases::MessageBatchSender;
use crate::std_prelude::*;

pub trait OfaFullRelayTypes:
    OfaRelayTypes<
    Runtime = Self::FullRuntime,
    SrcChain = Self::FullSrcChain,
    DstChain = Self::FullDstChain,
>
{
    type FullRuntime: OfaFullRuntime;

    type FullSrcChain: OfaFullIbcChain<
        Self::DstChain,
        Preset = Self::Preset,
        OutgoingPacket = Self::Packet,
    >;

    type FullDstChain: OfaFullIbcChain<
        Self::SrcChain,
        Preset = Self::Preset,
        IncomingPacket = Self::Packet,
        OutgoingPacket = <Self::SrcChain as OfaIbcChain<Self::DstChain>>::IncomingPacket,
    >;
}

#[async_trait]
pub trait OfaFullRelay: OfaFullRelayTypes + OfaBaseRelay {
    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error>;

    fn is_retryable_error(e: &Self::Error) -> bool;

    fn max_retry_exceeded_error(e: Self::Error) -> Self::Error;

    fn src_chain_message_batch_sender(&self) -> &MessageBatchSender<Self::SrcChain, Self::Error>;

    fn dst_chain_message_batch_sender(&self) -> &MessageBatchSender<Self::DstChain, Self::Error>;
}

impl<Relay> OfaFullRelayTypes for Relay
where
    Relay: OfaRelayTypes,
    Relay::Runtime: OfaFullRuntime,
    Relay::SrcChain: OfaFullChain,
    Relay::DstChain: OfaFullChain,
{
    type FullRuntime = Relay::Runtime;

    type FullSrcChain = Relay::SrcChain;

    type FullDstChain = Relay::DstChain;
}

pub trait OfaHomogeneousFullRelay:
    OfaFullRelayTypes<FullSrcChain = Self::Chain, FullDstChain = Self::Chain>
{
    type Chain: OfaFullIbcChain<
        Self::Chain,
        IncomingPacket = Self::Packet,
        OutgoingPacket = Self::Packet,
    >;
}

impl<Relay, Chain> OfaHomogeneousFullRelay for Relay
where
    Relay: OfaFullRelayTypes<FullSrcChain = Chain, FullDstChain = Chain>,
    Chain: OfaFullIbcChain<Chain, IncomingPacket = Self::Packet, OutgoingPacket = Self::Packet>,
{
    type Chain = Chain;
}
