use alloc::sync::Arc;
use ibc_relayer::chain::counterparty::counterparty_chain_from_channel;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{IncludeProof, QueryChannelRequest, QueryHeight};
use ibc_relayer_types::core::ics04_channel::channel::{
    ChannelEnd, Counterparty as ChannelCounterparty, State,
};
use ibc_relayer_types::core::ics04_channel::msgs::chan_open_confirm::MsgChannelOpenConfirm;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc_relayer_types::tx_msg::Msg;
use ibc_relayer_types::Height;

use crate::contexts::chain::CosmosChain;
use crate::methods::runtime::HasBlockingChainHandle;
use crate::traits::message::{wrap_cosmos_message, AsCosmosMessage, CosmosMessage};
use crate::types::channel::CosmosInitChannelOptions;
use crate::types::error::{BaseError, Error};
use crate::types::message::CosmosIbcMessage;
use crate::types::messages::channel_open_ack::CosmosChannelOpenAckMessage;
use crate::types::messages::channel_open_init::CosmosChannelOpenInitMessage;
use crate::types::messages::channel_open_try::CosmosChannelOpenTryMessage;
use crate::types::payloads::channel::{
    CosmosChannelOpenAckPayload, CosmosChannelOpenConfirmPayload, CosmosChannelOpenTryPayload,
};

pub async fn query_chain_id_from_channel_id<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    channel_id: &ChannelId,
    port_id: &PortId,
) -> Result<ChainId, Error> {
    let port_id = port_id.clone();
    let channel_id = channel_id.clone();

    chain
        .with_blocking_chain_handle(move |chain_handle| {
            let channel_id = counterparty_chain_from_channel(&chain_handle, &channel_id, &port_id)
                .map_err(BaseError::supervisor)?;

            Ok(channel_id)
        })
        .await
}

pub async fn build_channel_open_try_payload<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    height: &Height,
    port_id: &PortId,
    channel_id: &ChannelId,
) -> Result<CosmosChannelOpenTryPayload, Error> {
    let height = *height;
    let port_id = port_id.clone();
    let channel_id = channel_id.clone();

    chain
        .with_blocking_chain_handle(move |chain_handle| {
            let (channel_end, _) = chain_handle
                .query_channel(
                    QueryChannelRequest {
                        port_id: port_id.clone(),
                        channel_id: channel_id.clone(),
                        height: QueryHeight::Latest,
                    },
                    IncludeProof::No,
                )
                .map_err(BaseError::relayer)?;

            let proofs = chain_handle
                .build_channel_proofs(&port_id, &channel_id, height)
                .map_err(BaseError::relayer)?;

            let payload = CosmosChannelOpenTryPayload {
                ordering: channel_end.ordering,
                connection_hops: channel_end.connection_hops,
                version: channel_end.version,
                update_height: proofs.height(),
                proof_init: proofs.object_proof().clone(),
            };

            Ok(payload)
        })
        .await
}

pub async fn build_channel_open_ack_payload<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    height: &Height,
    port_id: &PortId,
    channel_id: &ChannelId,
) -> Result<CosmosChannelOpenAckPayload, Error> {
    let height = *height;
    let port_id = port_id.clone();
    let channel_id = channel_id.clone();

    chain
        .with_blocking_chain_handle(move |chain_handle| {
            let (channel_end, _) = chain_handle
                .query_channel(
                    QueryChannelRequest {
                        port_id: port_id.clone(),
                        channel_id: channel_id.clone(),
                        height: QueryHeight::Latest,
                    },
                    IncludeProof::No,
                )
                .map_err(BaseError::relayer)?;

            let proofs = chain_handle
                .build_channel_proofs(&port_id, &channel_id, height)
                .map_err(BaseError::relayer)?;

            let payload = CosmosChannelOpenAckPayload {
                version: channel_end.version,
                update_height: proofs.height(),
                proof_try: proofs.object_proof().clone(),
            };

            Ok(payload)
        })
        .await
}

pub async fn build_channel_open_confirm_payload<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    height: &Height,
    port_id: &PortId,
    channel_id: &ChannelId,
) -> Result<CosmosChannelOpenConfirmPayload, Error> {
    let height = *height;
    let port_id = port_id.clone();
    let channel_id = channel_id.clone();

    chain
        .with_blocking_chain_handle(move |chain_handle| {
            let proofs = chain_handle
                .build_channel_proofs(&port_id, &channel_id, height)
                .map_err(BaseError::relayer)?;

            let payload = CosmosChannelOpenConfirmPayload { proofs };

            Ok(payload)
        })
        .await
}

pub fn build_channel_open_init_message(
    port_id: &PortId,
    counterparty_port_id: &PortId,
    init_channel_options: &CosmosInitChannelOptions,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let port_id = port_id.clone();
    let ordering = init_channel_options.ordering;
    let connection_hops = init_channel_options.connection_hops.clone();
    let channel_version = init_channel_options.channel_version.clone();

    let counterparty = ChannelCounterparty::new(counterparty_port_id.clone(), None);

    let channel = ChannelEnd::new(
        State::Init,
        ordering,
        counterparty,
        connection_hops,
        channel_version,
    );

    let message = CosmosChannelOpenInitMessage { port_id, channel };

    Ok(message.to_cosmos_message())
}

pub fn build_channel_open_try_message(
    port_id: &PortId,
    counterparty_port_id: &PortId,
    counterparty_channel_id: &ChannelId,
    counterparty_payload: CosmosChannelOpenTryPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let port_id = port_id.clone();
    let counterparty = ChannelCounterparty::new(
        counterparty_port_id.clone(),
        Some(counterparty_channel_id.clone()),
    );
    let ordering = counterparty_payload.ordering;
    let connection_hops = counterparty_payload.connection_hops.clone();
    let version = counterparty_payload.version.clone();

    let channel = ChannelEnd::new(
        State::TryOpen,
        ordering,
        counterparty,
        connection_hops,
        version.clone(),
    );

    let message = CosmosChannelOpenTryMessage {
        port_id,
        channel,
        counterparty_version: version,
        update_height: counterparty_payload.update_height,
        proof_init: counterparty_payload.proof_init,
    };

    Ok(message.to_cosmos_message())
}

pub fn build_channel_open_ack_message(
    port_id: &PortId,
    channel_id: &ChannelId,
    counterparty_channel_id: &ChannelId,
    counterparty_payload: CosmosChannelOpenAckPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let message = CosmosChannelOpenAckMessage {
        port_id: port_id.clone(),
        channel_id: channel_id.clone(),
        counterparty_channel_id: counterparty_channel_id.clone(),
        counterparty_version: counterparty_payload.version,
        update_height: counterparty_payload.update_height,
        proof_try: counterparty_payload.proof_try,
    };

    Ok(message.to_cosmos_message())
}

pub fn build_channel_open_confirm_message(
    port_id: &PortId,
    channel_id: &ChannelId,
    counterparty_payload: CosmosChannelOpenConfirmPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let port_id = port_id.clone();
    let channel_id = channel_id.clone();
    let proofs = counterparty_payload.proofs.clone();

    let message = CosmosIbcMessage::new(None, move |signer| {
        let message = MsgChannelOpenConfirm {
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            proofs: proofs.clone(),
            signer: signer.clone(),
        };

        Ok(message.to_any())
    });

    Ok(wrap_cosmos_message(message))
}
