use async_trait::async_trait;
use core::iter::Iterator;
use core::time::Duration;

use crate::chain::traits::message_builders::connection::{
    CanBuildConnectionHandshakeMessages, CanBuildConnectionHandshakePayloads,
};
use crate::chain::traits::message_sender::CanSendSingleMessage;
use crate::chain::traits::types::connection::HasConnectionVersionType;
use crate::chain::traits::types::ibc_events::connection::HasConnectionOpenInitEvent;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::connection::open_init::ConnectionInitializer;
use crate::std_prelude::*;

pub trait InjectMissingConnectionInitEventError: HasRelayChains {
    fn missing_connection_init_event_error(&self) -> Self::Error;
}

pub struct InitializeConnection;

#[async_trait]
impl<Relay, SrcChain, DstChain> ConnectionInitializer<Relay> for InitializeConnection
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + InjectMissingConnectionInitEventError,
    SrcChain: CanSendSingleMessage
        + HasConnectionVersionType<DstChain>
        + CanBuildConnectionHandshakeMessages<DstChain>
        + HasConnectionOpenInitEvent<DstChain>,
    DstChain: CanBuildConnectionHandshakePayloads<SrcChain>,
    SrcChain::ConnectionId: Clone,
{
    async fn init_connection(
        relay: &Relay,
        connection_version: &SrcChain::ConnectionVersion,
        delay_period: Duration,
    ) -> Result<SrcChain::ConnectionId, Relay::Error> {
        let src_chain = relay.src_chain();
        let dst_chain = relay.dst_chain();

        let src_client_id = relay.src_client_id();
        let dst_client_id = relay.dst_client_id();

        let open_init_payload = dst_chain
            .build_connection_open_init_payload()
            .await
            .map_err(Relay::dst_chain_error)?;

        let src_message = src_chain
            .build_connection_open_init_message(
                src_client_id,
                dst_client_id,
                connection_version,
                delay_period,
                open_init_payload,
            )
            .await
            .map_err(Relay::src_chain_error)?;

        let events = src_chain
            .send_message(src_message)
            .await
            .map_err(Relay::src_chain_error)?;

        let open_init_event = events
            .into_iter()
            .find_map(|event| SrcChain::try_extract_connection_open_init_event(event))
            .ok_or_else(|| relay.missing_connection_init_event_error())?;

        let src_connection_id =
            SrcChain::connection_open_init_event_connection_id(&open_init_event);

        Ok(src_connection_id.clone())
    }
}
