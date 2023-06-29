use async_trait::async_trait;
use core::iter::Iterator;

use crate::chain::traits::connection::proofs::CanBuildConnectionProofs;
use crate::chain::traits::message_builders::connection::{
    CanBuildConnectionHandshakeMessages, CanBuildConnectionHandshakePayloads,
};
use crate::chain::traits::message_sender::CanSendMessages;
use crate::chain::traits::queries::connection::CanQueryConnection;
use crate::chain::traits::queries::status::CanQueryChainStatus;
use crate::chain::traits::types::height::HasHeightType;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::ibc_events::connection::HasConnectionOpenTryEvent;
use crate::chain::traits::wait::CanWaitChainSurpassHeight;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::connection::open_try::ConnectionOpenTryRelayer;
use crate::relay::traits::messages::update_client::CanBuildUpdateClientMessage;
use crate::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::std_prelude::*;

pub trait InjectMissingConnectionTryEventError: HasRelayChains {
    fn missing_connection_try_event_error(
        &self,
        src_connection_id: &<Self::SrcChain as HasIbcChainTypes<Self::DstChain>>::ConnectionId,
    ) -> Self::Error;
}

pub struct RelayConnectionOpenTry;

#[async_trait]
impl<Relay, SrcChain, DstChain, OpenTryEvent> ConnectionOpenTryRelayer<Relay>
    for RelayConnectionOpenTry
where
    Relay: HasRelayChains<SrcChain = SrcChain, DstChain = DstChain>
        + CanBuildUpdateClientMessage<SourceTarget>
        + CanBuildUpdateClientMessage<DestinationTarget>
        + InjectMissingConnectionTryEventError,
    DstChain: CanSendMessages
        + CanQueryChainStatus
        + CanWaitChainSurpassHeight
        + CanBuildConnectionHandshakeMessages<SrcChain>
        + HasConnectionOpenTryEvent<SrcChain, ConnectionOpenTryEvent = OpenTryEvent>,
    SrcChain: CanSendMessages
        + CanQueryChainStatus
        + CanQueryConnection<DstChain>
        + CanBuildConnectionProofs<DstChain>
        + CanBuildConnectionHandshakePayloads<DstChain>,
{
    async fn relay_connection_open_try(
        relay: &Relay,
        connection_id: &<Relay::SrcChain as HasIbcChainTypes<Relay::DstChain>>::ConnectionId,
    ) -> Result<OpenTryEvent, Relay::Error> {
        let src_chain = relay.src_chain();
        let dst_chain = relay.dst_chain();

        let dst_status = dst_chain
            .query_chain_status()
            .await
            .map_err(Relay::dst_chain_error)?;

        let dst_height = Relay::DstChain::chain_status_height(&dst_status);

        let src_update_client_messages = relay
            .build_update_client_messages(SourceTarget, dst_height)
            .await?;

        src_chain
            .send_messages(src_update_client_messages)
            .await
            .map_err(Relay::src_chain_error)?;

        let src_status = src_chain
            .query_chain_status()
            .await
            .map_err(Relay::src_chain_error)?;

        let src_height: &<SrcChain as HasHeightType>::Height =
            Relay::SrcChain::chain_status_height(&src_status);

        let update_client_messages = relay
            .build_update_client_messages(DestinationTarget, src_height)
            .await?;

        let open_try_payload = src_chain
            .build_connection_open_try_payload(src_height, relay.src_client_id(), connection_id)
            .await
            .map_err(Relay::src_chain_error)?;

        let open_try_message = dst_chain
            .build_connection_open_try_message(relay.dst_client_id(), open_try_payload)
            .await
            .map_err(Relay::dst_chain_error)?;

        let dst_messages = {
            let mut messages = update_client_messages;
            messages.push(open_try_message);
            messages
        };

        dst_chain
            .wait_chain_surpass_height(dst_height)
            .await
            .map_err(Relay::dst_chain_error)?;

        let mut events = dst_chain
            .send_messages(dst_messages)
            .await
            .map_err(Relay::dst_chain_error)?;

        let open_try_event = events
            .pop()
            .ok_or_else(|| relay.missing_connection_try_event_error(connection_id))?
            .into_iter()
            .find_map(|event| DstChain::try_extract_connection_open_try_event(event))
            .ok_or_else(|| relay.missing_connection_try_event_error(connection_id))?;

        Ok(open_try_event)
    }
}
