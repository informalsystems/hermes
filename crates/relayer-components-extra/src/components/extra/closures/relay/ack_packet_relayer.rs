use ibc_relayer_components::chain::traits::client::client_state::CanQueryClientState;
use ibc_relayer_components::chain::traits::client::consensus_state::CanFindConsensusStateHeight;
use ibc_relayer_components::chain::traits::client::update::{
    CanBuildUpdateClientMessage, CanBuildUpdateClientPayload,
};
use ibc_relayer_components::chain::traits::components::chain_status_querier::CanQueryChainStatus;
use ibc_relayer_components::chain::traits::components::consensus_state_querier::CanQueryConsensusState;
use ibc_relayer_components::chain::traits::components::message_sender::CanSendMessages;
use ibc_relayer_components::chain::traits::message_builders::ack_packet::{
    CanBuildAckPacketMessage, CanBuildAckPacketPayload,
};
use ibc_relayer_components::chain::traits::types::chain_id::HasChainId;
use ibc_relayer_components::chain::traits::types::client_state::HasClientStateFields;
use ibc_relayer_components::chain::traits::types::consensus_state::HasConsensusStateType;
use ibc_relayer_components::chain::traits::types::height::CanIncrementHeight;
use ibc_relayer_components::chain::traits::types::ibc::HasCounterpartyMessageHeight;
use ibc_relayer_components::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use ibc_relayer_components::chain::traits::types::packet::HasIbcPacketFields;
use ibc_relayer_components::core::traits::component::HasComponents;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::logger::traits::has_logger::HasLogger;
use ibc_relayer_components::logger::traits::level::HasBaseLogLevels;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::components::packet_relayers::ack_packet::CanRelayAckPacket;
use ibc_relayer_components::relay::traits::target::SourceTarget;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;

use crate::batch::traits::channel::HasMessageBatchSender;
use crate::components::extra::relay::ExtraRelayComponents;
use crate::runtime::traits::channel::CanUseChannels;
use crate::runtime::traits::channel_once::{CanCreateChannelsOnce, CanUseChannelsOnce};

pub trait CanUseExtraAckPacketRelayer: UseExtraAckPacketRelayer
where
    Self::DstChain: HasWriteAcknowledgementEvent<Self::SrcChain>,
{
}

pub trait UseExtraAckPacketRelayer: CanRelayAckPacket
where
    Self::DstChain: HasWriteAcknowledgementEvent<Self::SrcChain>,
{
}

impl<Relay, SrcChain, DstChain, BaseRelayComponents> UseExtraAckPacketRelayer for Relay
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + HasLogger
        + HasMessageBatchSender<SourceTarget>
        + HasComponents<Components = ExtraRelayComponents<BaseRelayComponents>>,
    SrcChain: HasErrorType
        + HasRuntime
        + HasChainId
        + CanSendMessages
        + HasConsensusStateType<DstChain>
        + HasCounterpartyMessageHeight<DstChain>
        + HasIbcPacketFields<DstChain, OutgoingPacket = Relay::Packet>
        + CanQueryClientState<DstChain>
        + CanQueryConsensusState<DstChain>
        + CanFindConsensusStateHeight<DstChain>
        + CanBuildAckPacketMessage<DstChain>
        + CanBuildUpdateClientMessage<DstChain>,
    DstChain: HasErrorType
        + HasRuntime
        + HasChainId
        + CanIncrementHeight
        + CanQueryChainStatus
        + HasClientStateFields<SrcChain>
        + HasConsensusStateType<SrcChain>
        + HasIbcPacketFields<SrcChain, IncomingPacket = Relay::Packet>
        + CanBuildAckPacketPayload<SrcChain>
        + CanBuildUpdateClientPayload<SrcChain>,
    SrcChain::Height: Clone,
    DstChain::Height: Clone,
    SrcChain::Runtime: CanCreateChannelsOnce + CanUseChannels + CanUseChannelsOnce,
    DstChain::Runtime: CanSleep,
    Relay::Logger: HasBaseLogLevels,
    BaseRelayComponents: Async,
{
}
