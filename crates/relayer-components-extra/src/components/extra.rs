use core::marker::PhantomData;

use crate::std_prelude::*;
use crate::telemetry::impls::status::ChainStatusTelemetryQuerier;
use ibc_relayer_components::relay::impls::client::update::BuildUpdateClientMessages;
use ibc_relayer_components::relay::impls::messages::skip_update_client::SkipUpdateClient;
use ibc_relayer_components::relay::impls::messages::wait_update_client::WaitUpdateClient;

pub struct ExtraComponents<BaseComponents>(pub PhantomData<BaseComponents>);

ibc_relayer_components::derive_update_client_message_builder!(
    ExtraComponents<BaseComponents>,
    SkipUpdateClient<WaitUpdateClient<BuildUpdateClientMessages>>,
);

ibc_relayer_components::derive_chain_status_querier!(
    ExtraComponents<BaseComponents>,
    ChainStatusTelemetryQuerier<BaseComponents>,
);
