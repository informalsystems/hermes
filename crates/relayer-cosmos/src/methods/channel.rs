use alloc::sync::Arc;
use ibc_relayer::chain::counterparty::counterparty_chain_from_channel;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{IncludeProof, QueryChannelRequest, QueryHeight};
use ibc_relayer_types::core::ics04_channel::channel::{
    ChannelEnd, Counterparty as ChannelCounterparty, State,
};
use ibc_relayer_types::core::ics04_channel::msgs::chan_open_ack::MsgChannelOpenAck;
use ibc_relayer_types::core::ics04_channel::msgs::chan_open_confirm::MsgChannelOpenConfirm;
use ibc_relayer_types::core::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
use ibc_relayer_types::core::ics04_channel::msgs::chan_open_try::MsgChannelOpenTry;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc_relayer_types::tx_msg::Msg;
use ibc_relayer_types::Height;

use crate::contexts::chain::CosmosChain;
use crate::traits::message::{wrap_cosmos_message, CosmosMessage};
use crate::types::channel::{
    CosmosChannelOpenAckPayload, CosmosChannelOpenConfirmPayload, CosmosChannelOpenTryPayload,
    CosmosInitChannelOptions,
};
use crate::types::error::{BaseError, Error};
use crate::types::message::CosmosIbcMessage;

pub async fn query_chain_id_from_channel_id<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    channel_id: &ChannelId,
    port_id: &PortId,
) -> Result<ChainId, Error> {
    let chain_handle = chain.handle.clone();

    let port_id = port_id.clone();
    let channel_id = channel_id.clone();

    chain
        .runtime
        .runtime
        .runtime
        .spawn_blocking(move || {
            let channel_id = counterparty_chain_from_channel(&chain_handle, &channel_id, &port_id)
                .map_err(BaseError::supervisor)?;

            Ok(channel_id)
        })
        .await
        .map_err(BaseError::join)?
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
    let chain_handle = chain.handle.clone();

    chain
        .runtime
        .runtime
        .runtime
        .spawn_blocking(move || {
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
                previous_channel_id: channel_end.counterparty().channel_id.clone(),
                proofs,
                ordering: channel_end.ordering,
                connection_hops: channel_end.connection_hops,
                version: channel_end.version,
            };

            Ok(payload)
        })
        .await
        .map_err(BaseError::join)?
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
    let chain_handle = chain.handle.clone();

    chain
        .runtime
        .runtime
        .runtime
        .spawn_blocking(move || {
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
                proofs,
                version: channel_end.version,
            };

            Ok(payload)
        })
        .await
        .map_err(BaseError::join)?
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
    let chain_handle = chain.handle.clone();

    chain
        .runtime
        .runtime
        .runtime
        .spawn_blocking(move || {
            let proofs = chain_handle
                .build_channel_proofs(&port_id, &channel_id, height)
                .map_err(BaseError::relayer)?;

            let payload = CosmosChannelOpenConfirmPayload { proofs };

            Ok(payload)
        })
        .await
        .map_err(BaseError::join)?
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

    let message = CosmosIbcMessage::new(None, move |signer| {
        let message = MsgChannelOpenInit {
            port_id: port_id.clone(),
            channel: channel.clone(),
            signer: signer.clone(),
        };

        Ok(message.to_any())
    });

    Ok(wrap_cosmos_message(message))
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
    let previous_channel_id = counterparty_payload.previous_channel_id.clone();
    let proofs = counterparty_payload.proofs.clone();

    let channel = ChannelEnd::new(
        State::TryOpen,
        ordering,
        counterparty,
        connection_hops,
        version.clone(),
    );

    let message = CosmosIbcMessage::new(None, move |signer| {
        let message = MsgChannelOpenTry {
            port_id: port_id.clone(),
            previous_channel_id: previous_channel_id.clone(),
            channel: channel.clone(),
            counterparty_version: version.clone(),
            proofs: proofs.clone(),
            signer: signer.clone(),
        };

        Ok(message.to_any())
    });

    Ok(wrap_cosmos_message(message))
}

pub fn build_channel_open_ack_message(
    port_id: &PortId,
    channel_id: &ChannelId,
    counterparty_channel_id: &ChannelId,
    counterparty_payload: CosmosChannelOpenAckPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let port_id = port_id.clone();
    let channel_id = channel_id.clone();
    let counterparty_channel_id = counterparty_channel_id.clone();
    let counterparty_version = counterparty_payload.version.clone();
    let proofs = counterparty_payload.proofs.clone();

    let message = CosmosIbcMessage::new(None, move |signer| {
        let message = MsgChannelOpenAck {
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            counterparty_channel_id: counterparty_channel_id.clone(),
            counterparty_version: counterparty_version.clone(),
            proofs: proofs.clone(),
            signer: signer.clone(),
        };

        Ok(message.to_any())
    });

    Ok(wrap_cosmos_message(message))
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
