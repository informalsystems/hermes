pub mod message_builders;
pub mod message_sender;
pub mod packet_relayers;
pub mod types;

use async_trait::async_trait;

use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaChainTypes};
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::impls::packet_relayers::general::retry::SupportsPacketRetry;
use crate::base::relay::traits::ibc_message_sender::InjectMismatchIbcEventsCountError;
use crate::base::relay::traits::messages::ack_packet::{
    AckPacketMessageBuilder, HasAckPacketMessageBuilder,
};
use crate::base::relay::traits::messages::timeout_packet::{
    HasTimeoutUnorderedPacketMessageBuilder, TimeoutUnorderedPacketMessageBuilder,
};
use crate::std_prelude::*;

pub struct OfaAckPacketMessageBuilder;

#[async_trait]
impl<Relay, SrcChain> AckPacketMessageBuilder<OfaRelayWrapper<Relay>> for OfaAckPacketMessageBuilder
where
    Relay: OfaBaseRelay<SrcChain = SrcChain>,
    SrcChain: OfaBaseChain,
{
    async fn build_ack_packet_message(
        relay: &OfaRelayWrapper<Relay>,
        destination_height: &<Relay::DstChain as OfaChainTypes>::Height,
        packet: &Relay::Packet,
        ack: &<Relay::DstChain as OfaChainTypes>::WriteAcknowledgementEvent,
    ) -> Result<SrcChain::Message, Relay::Error> {
        let message = relay
            .relay
            .build_ack_packet_message(destination_height, packet, ack)
            .await?;

        Ok(message)
    }
}

impl<Relay: OfaBaseRelay> HasAckPacketMessageBuilder for OfaRelayWrapper<Relay> {
    type AckPacketMessageBuilder = OfaAckPacketMessageBuilder;
}

/// Implements the timeout packet message builder that constructs timeout packets
/// to be sent over unordered channels between chains that implement the
/// [`one_for_all`] trait.
pub struct OfaTimeoutUnorderedPacketMessageBuilder;

#[async_trait]
impl<Relay, DstChain, SrcChain> TimeoutUnorderedPacketMessageBuilder<OfaRelayWrapper<Relay>>
    for OfaTimeoutUnorderedPacketMessageBuilder
where
    Relay: OfaBaseRelay<DstChain = DstChain, SrcChain = SrcChain>,
    DstChain: OfaBaseChain,
    SrcChain: OfaBaseChain,
{
    async fn build_timeout_unordered_packet_message(
        relay: &OfaRelayWrapper<Relay>,
        destination_height: &<Relay::DstChain as OfaChainTypes>::Height,
        packet: &Relay::Packet,
    ) -> Result<SrcChain::Message, Relay::Error> {
        let message = relay
            .relay
            .build_timeout_unordered_packet_message(destination_height, packet)
            .await?;

        Ok(message)
    }
}

impl<Relay: OfaBaseRelay> HasTimeoutUnorderedPacketMessageBuilder for OfaRelayWrapper<Relay> {
    type TimeoutUnorderedPacketMessageBuilder = OfaTimeoutUnorderedPacketMessageBuilder;
}

impl<Relay: OfaBaseRelay> SupportsPacketRetry for OfaRelayWrapper<Relay> {
    const MAX_RETRY: usize = 3;

    fn is_retryable_error(e: &Self::Error) -> bool {
        Relay::is_retryable_error(e)
    }

    fn max_retry_exceeded_error(e: Self::Error) -> Self::Error {
        Relay::max_retry_exceeded_error(e)
    }
}

impl<Relay: OfaBaseRelay> InjectMismatchIbcEventsCountError for OfaRelayWrapper<Relay> {
    fn mismatch_ibc_events_count_error(expected: usize, actual: usize) -> Self::Error {
        Relay::mismatch_ibc_events_count_error(expected, actual)
    }
}
