use core::marker::PhantomData;

use crate::chain::traits::queries::consensus_state::ConsensusStateQuerierComponent;
use crate::chain::traits::queries::status::ChainStatusQuerierComponent;
use crate::relay::components::auto_relayers::concurrent_bidirectional::ConcurrentBidirectionalRelayer;
use crate::relay::components::auto_relayers::concurrent_event::ConcurrentEventSubscriptionRelayer;
use crate::relay::components::auto_relayers::concurrent_two_way::ConcurrentTwoWayAutoRelay;
use crate::relay::components::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::relay::components::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::relay::components::packet_relayers::ack::base_ack_packet::BaseAckPacketRelayer;
use crate::relay::components::packet_relayers::general::filter_relayer::FilterRelayer;
use crate::relay::components::packet_relayers::general::full_relay::FullCycleRelayer;
use crate::relay::components::packet_relayers::general::lock::LockPacketRelayer;
use crate::relay::components::packet_relayers::general::log::LoggerRelayer;
use crate::relay::components::packet_relayers::receive::base_receive_packet::BaseReceivePacketRelayer;
use crate::relay::components::packet_relayers::receive::skip_received_packet::SkipReceivedPacketRelayer;
use crate::relay::components::packet_relayers::timeout_unordered::timeout_unordered_packet::BaseTimeoutUnorderedPacketRelayer;
use crate::relay::components::update_client::build::BuildUpdateClientMessages;
use crate::relay::components::update_client::skip::SkipUpdateClient;
use crate::relay::components::update_client::wait::WaitUpdateClient;
use crate::relay::traits::auto_relayer::{AutoRelayerComponent, BiRelayMode, RelayMode};
use crate::relay::traits::ibc_message_sender::{IbcMessageSenderComponent, MainSink};
use crate::relay::traits::messages::update_client::UpdateClientMessageBuilderComponent;
use crate::relay::traits::packet_filter::PacketFilterComponent;
use crate::relay::traits::packet_relayer::PacketRelayerComponent;
use crate::relay::traits::packet_relayers::ack_packet::AckPacketRelayerComponent;
use crate::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayerComponnent;
use crate::relay::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayerComponent;

pub struct DefaultComponents<BaseComponents>(pub PhantomData<BaseComponents>);

crate::forward_component!(
    ChainStatusQuerierComponent,
    DefaultComponents<BaseComponents>,
    BaseComponents,
);

crate::forward_component!(
    ConsensusStateQuerierComponent,
    DefaultComponents<BaseComponents>,
    BaseComponents
);

crate::forward_component!(
    IbcMessageSenderComponent<MainSink>,
    DefaultComponents<BaseComponents>,
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>,
);

crate::forward_component!(
    UpdateClientMessageBuilderComponent,
    DefaultComponents<BaseComponents>,
    SkipUpdateClient<WaitUpdateClient<BuildUpdateClientMessages>>,
);

crate::forward_component!(
    PacketRelayerComponent,
    DefaultComponents<BaseComponents>,
    LockPacketRelayer<LoggerRelayer<FilterRelayer<FullCycleRelayer>>>,
);

crate::forward_component!(
    PacketFilterComponent,
    DefaultComponents<BaseComponents>,
    BaseComponents,
);

crate::forward_component!(
    ReceivePacketRelayerComponnent,
    DefaultComponents<BaseComponents>,
    SkipReceivedPacketRelayer<BaseReceivePacketRelayer>,
);

crate::forward_component!(
    AckPacketRelayerComponent,
    DefaultComponents<BaseComponents>,
    BaseAckPacketRelayer,
);

crate::forward_component!(
    TimeoutUnorderedPacketRelayerComponent,
    DefaultComponents<BaseComponents>,
    BaseTimeoutUnorderedPacketRelayer,
);

crate::forward_component!(
    AutoRelayerComponent<RelayMode>,
    DefaultComponents<BaseComponents>,
    ConcurrentBidirectionalRelayer<ConcurrentEventSubscriptionRelayer>,
);

crate::forward_component!(
    AutoRelayerComponent<BiRelayMode>,
    DefaultComponents<BaseComponents>,
    ConcurrentTwoWayAutoRelay,
);
