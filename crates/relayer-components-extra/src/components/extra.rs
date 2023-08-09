use core::marker::PhantomData;

use crate::relay::impls::auto_relayers::parallel_bidirectional::ParallelBidirectionalRelayer;
use crate::relay::impls::auto_relayers::parallel_event::ParallelEventSubscriptionRelayer;
use crate::relay::impls::packet_relayers::retry::RetryRelayer;
use crate::std_prelude::*;
use crate::telemetry::impls::status::ChainStatusTelemetryQuerier;
use ibc_relayer_components::relay::impls::client::update::BuildUpdateClientMessages;
use ibc_relayer_components::relay::impls::messages::skip_update_client::SkipUpdateClient;
use ibc_relayer_components::relay::impls::messages::wait_update_client::WaitUpdateClient;
use ibc_relayer_components::relay::impls::packet_relayers::general::filter_relayer::FilterRelayer;
use ibc_relayer_components::relay::impls::packet_relayers::general::full_relay::FullCycleRelayer;
use ibc_relayer_components::relay::impls::packet_relayers::general::lock::LockPacketRelayer;
use ibc_relayer_components::relay::impls::packet_relayers::general::log::LoggerRelayer;

pub struct ExtraComponents<BaseComponents>(pub PhantomData<BaseComponents>);

ibc_relayer_components::derive_update_client_message_builder!(
    ExtraComponents<BaseComponents>,
    SkipUpdateClient<WaitUpdateClient<BuildUpdateClientMessages>>,
);

ibc_relayer_components::derive_chain_status_querier!(
    ExtraComponents<BaseComponents>,
    ChainStatusTelemetryQuerier<BaseComponents>,
);

ibc_relayer_components::derive_packet_relayer!(
    ExtraComponents<BaseComponents>,
    LockPacketRelayer<LoggerRelayer<FilterRelayer<RetryRelayer<FullCycleRelayer>>>>,
);

ibc_relayer_components::derive_auto_relayer!(
    ExtraComponents<BaseComponents>,
    ParallelBidirectionalRelayer<ParallelEventSubscriptionRelayer>,
);
