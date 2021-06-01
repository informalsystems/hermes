use thiserror::Error;
use tracing::error;

use ibc::application::ics20_fungible_token_transfer::msgs::transfer::MsgTransfer;
use ibc::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::tx_msg::Msg;

use crate::chain::{Chain, CosmosSdkChain};
use crate::config::ChainConfig;
use crate::error::Error;
use ibc::events::IbcEvent;
use ibc::timestamp::Timestamp;
use ibc::Height;
use std::time::Duration;

#[derive(Debug, Error)]
pub enum PacketError {
    #[error("failed with underlying cause: {0}")]
    Failed(String),

    #[error("key error with underlying cause: {0}")]
    Key(Error),

    #[error(
        "failed during a transaction submission step to chain id {0} with underlying error: {1}"
    )]
    Submit(ChainId, Error),

    #[error("timestamp overflow")]
    TimestampOverflow,
}

#[derive(Clone, Debug)]
pub struct TransferOptions {
    pub packet_src_chain_config: ChainConfig,
    pub packet_dst_chain_config: ChainConfig,
    pub packet_src_port_id: PortId,
    pub packet_src_channel_id: ChannelId,
    pub amount: u64,
    pub denom: String,
    pub receiver: Option<String>,
    pub timeout_height_offset: u64,
    pub timeout_seconds: Duration,
    pub number_msgs: usize,
}

pub fn build_and_send_transfer_messages(
    mut packet_src_chain: CosmosSdkChain, // the chain whose account is debited
    mut packet_dst_chain: CosmosSdkChain, // the chain where the transfer is sent
    opts: TransferOptions,
) -> Result<Vec<IbcEvent>, PacketError> {
    let receiver = match &opts.receiver {
        None => packet_dst_chain.get_signer(),
        Some(r) => Ok(r.clone().into()),
    }
    .map_err(PacketError::Key)?;

    let sender = packet_src_chain.get_signer().map_err(PacketError::Key)?;

    let timeout_timestamp = if opts.timeout_seconds == Duration::from_secs(0) {
        Timestamp::none()
    } else {
        (Timestamp::now() + opts.timeout_seconds).map_err(|_| PacketError::TimestampOverflow)?
    };

    let timeout_height = if opts.timeout_height_offset == 0 {
        Height::zero()
    } else {
        packet_dst_chain
            .query_latest_height()
            .map_err(|_| PacketError::Failed("Height error".to_string()))?
            .add(opts.timeout_height_offset)
    };

    let msg = MsgTransfer {
        source_port: opts.packet_src_port_id.clone(),
        source_channel: opts.packet_src_channel_id.clone(),
        token: Some(ibc_proto::cosmos::base::v1beta1::Coin {
            denom: opts.denom.clone(),
            amount: opts.amount.to_string(),
        }),
        sender,
        receiver,
        timeout_height,
        timeout_timestamp,
    };

    let raw_msg = msg.to_any();
    let msgs = vec![raw_msg; opts.number_msgs];

    let events = packet_src_chain
        .send_msgs(msgs)
        .map_err(|e| PacketError::Submit(packet_src_chain.id().clone(), e))?;

    // Check if the chain rejected the transaction
    let result = events
        .iter()
        .find(|event| matches!(event, IbcEvent::ChainError(_)));

    match result {
        None => Ok(events),
        Some(err) => {
            if let IbcEvent::ChainError(err) = err {
                Err(PacketError::Failed(err.to_string()))
            } else {
                panic!(
                    "internal error, expected IBCEvent::ChainError, got {:?}",
                    err
                )
            }
        }
    }
}
