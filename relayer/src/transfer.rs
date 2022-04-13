use core::fmt::{Display, Formatter};
use core::str::FromStr;
use core::time::Duration;

use flex_error::{define_error, DetailOnly};
use ibc::applications::ics20_fungible_token_transfer::msgs::transfer::MsgTransfer;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::events::IbcEvent;
use ibc::timestamp::{Timestamp, TimestampOverflowError};
use ibc::tx_msg::Msg;
use ibc::Height;
use uint::FromStrRadixErr;

use crate::chain::handle::ChainHandle;
use crate::chain::tx::TrackedMsgs;
use crate::chain::ChainStatus;
use crate::error::Error;
use crate::util::bigint::U256;

define_error! {
    TransferError {
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

        ZeroTimeout
            | _ | { "packet timeout height and packet timeout timestamp cannot both be 0" },
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Amount(pub U256);

impl Display for Amount {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl FromStr for Amount {
    type Err = FromStrRadixErr;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(U256::from_str_radix(s, 10)?))
    }
}

#[derive(Copy, Clone)]
pub struct TransferTimeout {
    pub timeout_height: Height,
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
            Height::zero()
        } else {
            destination_chain_status.height.add(timeout_height_offset)
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

pub fn build_and_send_transfer_messages<SrcChain: ChainHandle, DstChain: ChainHandle>(
    packet_src_chain: &SrcChain, // the chain whose account is debited
    packet_dst_chain: &DstChain, // the chain whose account eventually gets credited
    opts: &TransferOptions,
) -> Result<Vec<IbcEvent>, TransferError> {
    let receiver = match &opts.receiver {
        None => packet_dst_chain.get_signer().map_err(TransferError::key)?,
        Some(r) => r.clone().into(),
    };

    let sender = packet_src_chain.get_signer().map_err(TransferError::key)?;

    let chain_status = packet_dst_chain
        .query_status()
        .map_err(TransferError::relayer)?;

    let timeout = TransferTimeout::new(
        opts.timeout_height_offset,
        opts.timeout_duration,
        &chain_status,
    )?;

    let msg = MsgTransfer {
        source_port: opts.packet_src_port_id.clone(),
        source_channel: opts.packet_src_channel_id,
        token: Some(ibc_proto::cosmos::base::v1beta1::Coin {
            denom: opts.denom.clone(),
            amount: opts.amount.to_string(),
        }),
        sender,
        receiver,
        timeout_height: timeout.timeout_height,
        timeout_timestamp: timeout.timeout_timestamp,
    };

    let raw_msg = msg.to_any();
    let msgs = vec![raw_msg; opts.number_msgs];

    let events = packet_src_chain
        .send_messages_and_wait_commit(TrackedMsgs::new(msgs, "ft-transfer"))
        .map_err(|e| TransferError::submit(packet_src_chain.id(), e))?;

    // Check if the chain rejected the transaction
    let result = events
        .iter()
        .find(|event| matches!(event, IbcEvent::ChainError(_)));

    match result {
        None => Ok(events),
        Some(err) => {
            if let IbcEvent::ChainError(err) = err {
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
