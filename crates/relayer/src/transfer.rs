use core::time::Duration;
use std::{
    ops::Add,
    str::FromStr,
};

use flex_error::{
    define_error,
    DetailOnly,
};
use ibc_proto::{
    cosmos::base::v1beta1::Coin,
    google::protobuf::Any,
};
use ibc_relayer_types::{
    applications::transfer::{
        error::Error as Ics20Error,
        msgs::{
            transfer::MsgTransfer,
            ASTRIA_WITHDRAWAL_TYPE_URL,
        },
        Amount,
    },
    core::{
        ics04_channel::timeout::TimeoutHeight,
        ics24_host::identifier::{
            ChainId,
            ChannelId,
            PortId,
        },
    },
    events::IbcEvent,
    signer::{
        Signer,
        SignerError,
    },
    timestamp::{
        Timestamp,
        TimestampOverflowError,
    },
    tx_msg::Msg,
};
use prost::Message;

use crate::{
    chain::{
        endpoint::ChainStatus,
        handle::ChainHandle,
        tracking::TrackedMsgs,
    },
    error::Error,
    event::IbcEventWithHeight,
};

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
    pub src_port_id: PortId,
    pub src_channel_id: ChannelId,
    pub amount: Amount,
    pub denom: String,
    pub receiver: Option<String>,
    pub timeout_height_offset: u64,
    pub timeout_duration: Duration,
    pub number_msgs: usize,
    pub memo: Option<String>,
}

pub fn build_transfer_message(
    src_port_id: PortId,
    src_channel_id: ChannelId,
    amount: Amount,
    denom: String,
    sender: Signer,
    receiver: Signer,
    timeout_height: TimeoutHeight,
    timeout_timestamp: Timestamp,
    memo: Option<String>,
) -> Any {
    let msg = MsgTransfer {
        source_port: src_port_id,
        source_channel: src_channel_id,
        token: Coin {
            denom,
            amount: amount.to_string(),
        },
        sender,
        receiver,
        timeout_height,
        timeout_timestamp,
        memo,
    };

    msg.to_any()
}

fn build_transfer_message_astria(
    src_channel_id: ChannelId,
    amount: Amount,
    denom: String,
    sender: Signer,
    receiver: Signer,
    timeout_height: TimeoutHeight,
    timeout_timestamp: Timestamp,
) -> Any {
    let timeout_height = match timeout_height {
        // TODO: update astria IbcHeight to support optional?
        TimeoutHeight::At(height) => astria_core::generated::sequencer::v1alpha1::IbcHeight {
            revision_number: height.revision_number(),
            revision_height: height.revision_height(),
        },
        TimeoutHeight::Never => astria_core::generated::sequencer::v1alpha1::IbcHeight {
            revision_number: 0,
            revision_height: u64::MAX,
        },
    };

    let msg = astria_core::generated::sequencer::v1alpha1::Ics20Withdrawal {
        source_channel: src_channel_id.to_string(),
        denom: denom,
        amount: Some(
            u128::try_from(amount.0)
                .expect("amount can fit into u128")
                .into(),
        ),
        destination_chain_address: receiver.to_string(),
        return_address: hex::decode(sender.to_string()).expect("sender address is hex"),
        timeout_height: Some(timeout_height),
        timeout_time: timeout_timestamp.nanoseconds(),
    };

    Any {
        type_url: ASTRIA_WITHDRAWAL_TYPE_URL.to_string(),
        value: msg.encode_to_vec(),
    }
}

pub fn build_transfer_messages<SrcChain: ChainHandle, DstChain: ChainHandle>(
    src_chain: &SrcChain, // the chain whose account is debited
    dst_chain: &DstChain, // the chain whose account eventually gets credited
    opts: &TransferOptions,
) -> Result<Vec<Any>, TransferError> {
    let receiver = match &opts.receiver {
        Some(receiver) => Signer::from_str(receiver).map_err(TransferError::receiver_address)?,
        None => dst_chain.get_signer().map_err(TransferError::key)?,
    };

    let sender = src_chain.get_signer().map_err(TransferError::key)?;

    let destination_chain_status = dst_chain
        .query_application_status()
        .map_err(TransferError::relayer)?;

    let timeout = TransferTimeout::new(
        opts.timeout_height_offset,
        opts.timeout_duration,
        &destination_chain_status,
    )?;

    let message = if src_chain.id().as_str() == "astria" {
        build_transfer_message_astria(
            opts.src_channel_id.clone(),
            opts.amount,
            opts.denom.clone(),
            sender,
            receiver,
            timeout.timeout_height,
            timeout.timeout_timestamp,
        )
    } else {
        build_transfer_message(
            opts.src_port_id.clone(),
            opts.src_channel_id.clone(),
            opts.amount,
            opts.denom.clone(),
            sender,
            receiver,
            timeout.timeout_height,
            timeout.timeout_timestamp,
            opts.memo.clone(),
        )
    };

    let msgs = vec![message; opts.number_msgs];
    Ok(msgs)
}

pub fn send_messages<Chain: ChainHandle>(
    chain: &Chain,
    msgs: Vec<Any>,
) -> Result<Vec<IbcEventWithHeight>, TransferError> {
    let events_with_heights = chain
        .send_messages_and_wait_commit(TrackedMsgs::new_static(msgs, "ft-transfer"))
        .map_err(|e| TransferError::submit(chain.id(), e))?;

    // Check if the chain rejected the transaction
    let result = events_with_heights
        .iter()
        .find(|event| matches!(event.event, IbcEvent::ChainError(_)));

    match result {
        None => Ok(events_with_heights),
        Some(err) => {
            if let IbcEvent::ChainError(ref err) = err.event {
                Err(TransferError::tx_response(err.clone()))
            } else {
                panic!("internal error, expected IBCEvent::ChainError, got {err:?}")
            }
        }
    }
}

pub fn build_and_send_transfer_messages<SrcChain: ChainHandle, DstChain: ChainHandle>(
    // the chain whose account is debited
    src_chain: &SrcChain,
    // the chain whose account eventually gets credited
    dst_chain: &DstChain,
    // options describing the transfer
    opts: &TransferOptions,
) -> Result<Vec<IbcEventWithHeight>, TransferError> {
    let msgs = build_transfer_messages(src_chain, dst_chain, opts)?;
    send_messages(src_chain, msgs)
}
