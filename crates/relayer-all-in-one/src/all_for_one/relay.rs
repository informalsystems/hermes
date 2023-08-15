use ibc_relayer_components::chain::types::aliases::{IncomingPacket, OutgoingPacket};
use ibc_relayer_components::logger::traits::level::HasLoggerWithBaseLevels;
use ibc_relayer_components::relay::impls::client::create::CanCreateClient;
use ibc_relayer_components::relay::traits::auto_relayer::CanAutoRelay;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::channel::open_handshake::CanRelayChannelOpenHandshake;
use ibc_relayer_components::relay::traits::channel::open_init::CanInitChannel;
use ibc_relayer_components::relay::traits::connection::open_handshake::CanRelayConnectionOpenHandshake;
use ibc_relayer_components::relay::traits::connection::open_init::CanInitConnection;
use ibc_relayer_components::relay::traits::event_relayer::CanRelayEvent;
use ibc_relayer_components::relay::traits::ibc_message_sender::{CanSendIbcMessages, MainSink};
use ibc_relayer_components::relay::traits::packet::HasRelayPacket;
use ibc_relayer_components::relay::traits::packet_clear::CanClearReceivePackets;
use ibc_relayer_components::relay::traits::packet_filter::CanFilterPackets;
use ibc_relayer_components::relay::traits::packet_relayer::CanRelayPacket;
use ibc_relayer_components::relay::traits::packet_relayers::ack_packet::CanRelayAckPacket;
use ibc_relayer_components::relay::traits::packet_relayers::receive_packet::CanRelayReceivePacket;
use ibc_relayer_components::relay::traits::packet_relayers::timeout_unordered_packet::CanRelayTimeoutUnorderedPacket;
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_components::relay::traits::update_client::CanBuildUpdateClientMessage;
use ibc_relayer_components_extra::relay::components::packet_relayers::retry::SupportsPacketRetry;

use crate::all_for_one::chain::AfoChain;
use crate::all_for_one::runtime::HasAfoRuntime;

/// The functionality that a relay context gains access to once that relay
/// context implements the `OfaRelayWrapper` trait.
pub trait AfoRelay:
    Clone
    + HasAfoRuntime
    + HasLoggerWithBaseLevels
    + HasRelayChains<SrcChain = Self::AfoSrcChain, DstChain = Self::AfoDstChain>
    + HasRelayPacket<SrcChainWithPacket = Self::AfoSrcChain, DstChainWithPacket = Self::AfoDstChain>
    + CanBuildUpdateClientMessage<SourceTarget>
    + CanBuildUpdateClientMessage<DestinationTarget>
    + CanSendIbcMessages<MainSink, SourceTarget>
    + CanSendIbcMessages<MainSink, DestinationTarget>
    + CanRelayEvent<SourceTarget>
    + CanRelayEvent<DestinationTarget>
    + CanAutoRelay
    + CanFilterPackets
    + CanRelayReceivePacket
    + CanRelayPacket
    + CanRelayAckPacket
    + CanRelayTimeoutUnorderedPacket
    + CanCreateClient<SourceTarget>
    + CanCreateClient<DestinationTarget>
    + CanInitConnection
    + CanRelayConnectionOpenHandshake
    + CanInitChannel
    + CanRelayChannelOpenHandshake
    + SupportsPacketRetry
    + CanClearReceivePackets
{
    type AfoSrcChain: AfoChain<Self::AfoDstChain>;

    type AfoDstChain: AfoChain<
        Self::AfoSrcChain,
        IncomingPacket = OutgoingPacket<Self::AfoSrcChain, Self::AfoDstChain>,
        OutgoingPacket = IncomingPacket<Self::AfoSrcChain, Self::AfoDstChain>,
    >;
}

impl<Relay, SrcChain, DstChain, Packet, ReversePacket> AfoRelay for Relay
where
    SrcChain: AfoChain<DstChain, IncomingPacket = ReversePacket, OutgoingPacket = Packet>,
    DstChain: AfoChain<SrcChain, IncomingPacket = Packet, OutgoingPacket = ReversePacket>,
    Relay: Clone
        + HasAfoRuntime
        + HasLoggerWithBaseLevels
        + HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + HasRelayPacket<SrcChainWithPacket = SrcChain, DstChainWithPacket = DstChain>
        + CanBuildUpdateClientMessage<SourceTarget>
        + CanBuildUpdateClientMessage<DestinationTarget>
        + CanSendIbcMessages<MainSink, SourceTarget>
        + CanSendIbcMessages<MainSink, DestinationTarget>
        + CanRelayEvent<SourceTarget>
        + CanRelayEvent<DestinationTarget>
        + CanAutoRelay
        + CanFilterPackets
        + CanRelayReceivePacket
        + CanRelayPacket
        + CanRelayAckPacket
        + CanRelayTimeoutUnorderedPacket
        + CanCreateClient<SourceTarget>
        + CanCreateClient<DestinationTarget>
        + CanInitConnection
        + CanRelayConnectionOpenHandshake
        + CanInitChannel
        + CanRelayChannelOpenHandshake
        + SupportsPacketRetry
        + CanClearReceivePackets,
{
    type AfoSrcChain = SrcChain;

    type AfoDstChain = DstChain;
}
