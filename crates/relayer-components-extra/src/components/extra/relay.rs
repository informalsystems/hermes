use core::marker::PhantomData;

use ibc_relayer_components::components::default::relay::DefaultRelayComponents;
use ibc_relayer_components::relay::components::message_senders::chain_sender::SendIbcMessagesToChain;
use ibc_relayer_components::relay::components::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use ibc_relayer_components::relay::components::packet_relayers::general::filter_relayer::FilterRelayer;
use ibc_relayer_components::relay::components::packet_relayers::general::full_relay::FullCycleRelayer;
use ibc_relayer_components::relay::components::packet_relayers::general::lock::LockPacketRelayer;
use ibc_relayer_components::relay::components::packet_relayers::general::log::LoggerRelayer;
use ibc_relayer_components::relay::traits::auto_relayer::AutoRelayerComponent;
use ibc_relayer_components::relay::traits::ibc_message_sender::{
    IbcMessageSenderComponent, MainSink,
};
use ibc_relayer_components::relay::traits::messages::update_client::UpdateClientMessageBuilderComponent;
use ibc_relayer_components::relay::traits::packet_filter::PacketFilterComponent;
use ibc_relayer_components::relay::traits::packet_relayer::PacketRelayerComponent;
use ibc_relayer_components::relay::traits::packet_relayers::ack_packet::AckPacketRelayerComponent;
use ibc_relayer_components::relay::traits::packet_relayers::receive_packet::ReceivePacketRelayerComponnent;
use ibc_relayer_components::relay::traits::packet_relayers::timeout_unordered_packet::TimeoutUnorderedPacketRelayerComponent;

use crate::batch::components::message_sender::SendMessagesToBatchWorker;
use crate::batch::types::sink::BatchWorkerSink;
use crate::relay::components::auto_relayers::parallel_bidirectional::ParallelBidirectionalRelayer;
use crate::relay::components::auto_relayers::parallel_event::ParallelEventSubscriptionRelayer;
use crate::relay::components::packet_relayers::retry::RetryRelayer;

pub struct ExtraRelayComponents<BaseComponents>(pub PhantomData<BaseComponents>);

ibc_relayer_components::delegate_component!(
    IbcMessageSenderComponent<MainSink>,
    ExtraRelayComponents<BaseComponents>,
    SendMessagesToBatchWorker,
);

ibc_relayer_components::delegate_component!(
    IbcMessageSenderComponent<BatchWorkerSink>,
    ExtraRelayComponents<BaseComponents>,
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>,
);

ibc_relayer_components::delegate_component!(
    PacketRelayerComponent,
    ExtraRelayComponents<BaseComponents>,
    LockPacketRelayer<LoggerRelayer<FilterRelayer<RetryRelayer<FullCycleRelayer>>>>,
);

ibc_relayer_components::delegate_component!(
    AutoRelayerComponent,
    ExtraRelayComponents<BaseComponents>,
    ParallelBidirectionalRelayer<ParallelEventSubscriptionRelayer>,
);

ibc_relayer_components::delegate_components!(
    [
        UpdateClientMessageBuilderComponent,
        PacketFilterComponent,
        ReceivePacketRelayerComponnent,
        AckPacketRelayerComponent,
        TimeoutUnorderedPacketRelayerComponent,
    ],
    ExtraRelayComponents<BaseComponents>,
    DefaultRelayComponents<BaseComponents>,
);
