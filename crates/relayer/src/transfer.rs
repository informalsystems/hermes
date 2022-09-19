use ibc::signer::SignerError;
use std::str::FromStr;

use core::time::Duration;

use flex_error::{define_error, DetailOnly};
use ibc::applications::transfer::error::Error as Ics20Error;
use ibc::applications::transfer::msgs::transfer::MsgTransfer;
use ibc::applications::transfer::Amount;
use ibc::core::ics04_channel::timeout::TimeoutHeight;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::events::IbcEvent;
use ibc::signer::Signer;
use ibc::timestamp::{Timestamp, TimestampOverflowError};
use ibc::tx_msg::Msg;
use ibc_proto::cosmos::base::v1beta1::Coin;
use ibc_proto::google::protobuf::Any;

use crate::chain::endpoint::ChainStatus;
use crate::chain::handle::ChainHandle;
use crate::chain::tracking::TrackedMsgs;
use crate::error::Error;

define_error! {
    TransferError {
        ReceiverAddress
            [ SignerError ]
            |_| { "receiver address error "},
        Relayer
            [ Error ]
            |_| { "relayer error" },

        Key
            [ Error ]
            |_| { "key error" },

        Submit
            { chain_id: ChainId }
            [ Error ]
            |e| {
                format!("failed while submitting the Transfer message to chain {0}",
                    e.chain_id)
            },

        TimestampOverflow
            [ DetailOnly<TimestampOverflowError> ]
            |_| { "timestamp overflow" },

        TxResponse
            { event: String }
            |e| {
                format!("tx response event consists of an error: {}",
                    e.event)
            },

        UnexpectedEvent
            { event: IbcEvent }
            |e| {
                format!("internal error, expected IBCEvent::ChainError, got {:?}",
                    e.event)
            },

        TokenTransfer
            [ Ics20Error ]
            |_| { "token transfer error" },

        ZeroTimeout
            | _ | { "packet timeout height and packet timeout timestamp cannot both be 0" },
    }
}

#[derive(Copy, Clone)]
pub struct TransferTimeout {
    pub timeout_height: TimeoutHeight,
    pub timeout_timestamp: Timestamp,
}

impl TransferTimeout {
    /**
       Construct the transfer timeout parameters from the given timeout
       height offset, timeout duration, and the latest chain status
       containing the latest time of the destination chain.

       The height offset and duration are optional, with zero indicating
       that the packet do not get expired at the given height or time.
       If both height offset and duration are zero, then the packet will
       never expire.
    */
    pub fn new(
        timeout_height_offset: u64,
        timeout_duration: Duration,
        destination_chain_status: &ChainStatus,
    ) -> Result<Self, TransferError> {
        let timeout_height = if timeout_height_offset == 0 {
            TimeoutHeight::no_timeout()
        } else {
            destination_chain_status
                .height
                .add(timeout_height_offset)
                .into()
        };

        let timeout_timestamp = if timeout_duration == Duration::ZERO {
            Timestamp::none()
        } else {
            (destination_chain_status.timestamp + timeout_duration)
                .map_err(TransferError::timestamp_overflow)?
        };

        Ok(TransferTimeout {
            timeout_height,
            timeout_timestamp,
        })
    }
}

#[derive(Clone, Debug)]
pub struct TransferOptions {
    pub packet_src_port_id: PortId,
    pub packet_src_channel_id: ChannelId,
    pub amount: Amount,
    pub denom: String,
    pub receiver: Option<String>,
    pub timeout_height_offset: u64,
    pub timeout_duration: Duration,
    pub number_msgs: usize,
}

pub fn build_transfer_message(
    packet_src_port_id: PortId,
    packet_src_channel_id: ChannelId,
    amount: Amount,
    denom: String,
    sender: Signer,
    receiver: Signer,
    timeout_height: TimeoutHeight,
    timeout_timestamp: Timestamp,
) -> Any {
    let msg = MsgTransfer {
        source_port: packet_src_port_id,
        source_channel: packet_src_channel_id,
        token: Coin {
            denom,
            amount: amount.to_string(),
        },
        sender,
        receiver,
        timeout_height,
        timeout_timestamp,
    };

    msg.to_any()
}

pub fn build_and_send_transfer_messages<SrcChain: ChainHandle, DstChain: ChainHandle>(
    packet_src_chain: &SrcChain, // the chain whose account is debited
    packet_dst_chain: &DstChain, // the chain whose account eventually gets credited
    opts: &TransferOptions,
) -> Result<Vec<IbcEvent>, TransferError> {
    let receiver = match &opts.receiver {
        Some(receiver) => Signer::from_str(receiver).map_err(TransferError::receiver_address)?,
        None => packet_dst_chain.get_signer().map_err(TransferError::key)?,
    };

    let sender = packet_src_chain.get_signer().map_err(TransferError::key)?;

    let destination_chain_status = packet_dst_chain
        .query_application_status()
        .map_err(TransferError::relayer)?;

    let timeout = TransferTimeout::new(
        opts.timeout_height_offset,
        opts.timeout_duration,
        &destination_chain_status,
    )?;

    let msg = MsgTransfer {
        source_port: opts.packet_src_port_id.clone(),
        source_channel: opts.packet_src_channel_id.clone(),
        token: Coin {
            denom: opts.denom.clone(),
            amount: opts.amount.to_string(),
        },
        sender,
        receiver,
        timeout_height: timeout.timeout_height,
        timeout_timestamp: timeout.timeout_timestamp,
    };

    let raw_msg = msg.to_any();
    let msgs = vec![raw_msg; opts.number_msgs];

    let events_with_heights = packet_src_chain
        .send_messages_and_wait_commit(TrackedMsgs::new_static(msgs, "ft-transfer"))
        .map_err(|e| TransferError::submit(packet_src_chain.id(), e))?;

    // Check if the chain rejected the transaction
    let result = events_with_heights
        .iter()
        .find(|event| matches!(event.event, IbcEvent::ChainError(_)));

    match result {
        None => Ok(events_with_heights.into_iter().map(|ev| ev.event).collect()),
        Some(err) => {
            if let IbcEvent::ChainError(ref err) = err.event {
                Err(TransferError::tx_response(err.clone()))
            } else {
                panic!(
                    "internal error, expected IBCEvent::ChainError, got {:?}",
                    err
                )
            }
        }
    }
}
