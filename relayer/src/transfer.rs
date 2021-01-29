use crate::chain::{Chain, CosmosSDKChain};
use thiserror::Error;
use tracing::error;

use crate::config::ChainConfig;
use crate::error::Error;
use ibc::events::IBCEvent;
use ibc::ics24_host::identifier::{ChannelId, PortId};
use ibc::tx_msg::Msg;
use ibc::{
    application::ics20_fungible_token_transfer::msgs::transfer::MsgTransfer,
    ics24_host::identifier::ChainId,
};
use ibc_proto::ibc::applications::transfer::v1::MsgTransfer as RawMsgTransfer;

#[derive(Debug, Error)]
pub enum PacketError {
    #[error("failed {0}")]
    Failed(String),

    #[error("key error")]
    KeyError(String),

    #[error(
        "failed during a transaction submission step to chain id {0} with underlying error: {1}"
    )]
    SubmitError(ChainId, Error),
}

#[derive(Clone, Debug)]
pub struct TransferOptions {
    pub packet_src_chain_config: ChainConfig,
    pub packet_dst_chain_config: ChainConfig,
    pub packet_src_port_id: PortId,
    pub packet_src_channel_id: ChannelId,
    pub amount: u64,
    pub denom: String,
    pub height_offset: u64,
    pub number_msgs: usize,
}

pub fn build_and_send_transfer_messages(
    mut packet_src_chain: CosmosSDKChain, // the chain whose account is debited
    mut packet_dst_chain: CosmosSDKChain, // the chain where the transfer is sent
    opts: &TransferOptions,
) -> Result<Vec<IBCEvent>, PacketError> {
    let receiver = packet_dst_chain
        .get_signer()
        .map_err(|_e| PacketError::KeyError("Key error".to_string()))?;

    let sender = packet_src_chain
        .get_signer()
        .map_err(|_e| PacketError::KeyError("Key error".to_string()))?;

    let latest_height = packet_dst_chain
        .query_latest_height()
        .map_err(|_e| PacketError::Failed("Height error".to_string()))?;

    let msg = MsgTransfer {
        source_port: opts.packet_src_port_id.clone(),
        source_channel: opts.packet_src_channel_id.clone(),
        token: Some(ibc_proto::cosmos::base::v1beta1::Coin {
            denom: opts.denom.clone(),
            amount: opts.amount.to_string(),
        }),
        sender,
        receiver,
        timeout_height: latest_height.add(opts.height_offset),
        timeout_timestamp: 0,
    };

    let raw_msg = msg.to_any::<RawMsgTransfer>();
    let msgs = vec![raw_msg; opts.number_msgs];

    let events = packet_src_chain
        .send_msgs(msgs)
        .map_err(|e| PacketError::SubmitError(packet_src_chain.id().clone(), e))?;

    // Separate the error events from the packet send events
    let (err_events, ret_events): (Vec<IBCEvent>, Vec<IBCEvent>) = events
        .into_iter()
        .partition(|event| matches!(event, IBCEvent::ChainError(_e)));

    if err_events.is_empty() {
        Ok(ret_events)
    } else {
        match err_events[0].clone() {
            IBCEvent::ChainError(e) => Err(PacketError::Failed(format!(
                "tx response event consists of an error: {}",
                e
            ))),
            _ => panic!("internal error"),
        }
    }
}
