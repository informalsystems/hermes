use core::fmt::{Display, Error as FmtError, Formatter};

use tendermint_rpc::endpoint::broadcast::tx_sync;
use tracing::info;

use ibc::events::IbcEvent;

use crate::chain::handle::ChainHandle;
use crate::chain::tracking::TrackedMsgs;
use crate::link::error::LinkError;
use crate::link::RelaySummary;
use crate::util::pretty::{PrettyCode, PrettyEvents};

pub trait SubmitReply {
    /// Creates a new, empty instance, i.e., comprising zero replies.
    fn empty() -> Self;

    /// Counts the number of replies that this instance contains.
    fn len(&self) -> usize;
}

impl SubmitReply for RelaySummary {
    fn empty() -> Self {
        RelaySummary::empty()
    }

    fn len(&self) -> usize {
        self.events.len()
    }
}

/// Captures the ability to submit messages to a chain.
pub trait Submit {
    type Reply: SubmitReply;

    fn submit(target: &impl ChainHandle, msgs: TrackedMsgs) -> Result<Self::Reply, LinkError>;
}

/// Synchronous sender
pub struct SyncSender;

impl Submit for SyncSender {
    type Reply = RelaySummary;

    // TODO: Switch from the `Chain::send_msgs` interface in this method
    //  to use `Chain::submit_msgs` instead; implement waiting for block
    //  commits directly here (instead of blocking in the chain runtime).
    fn submit(target: &impl ChainHandle, msgs: TrackedMsgs) -> Result<Self::Reply, LinkError> {
        let tx_events = target
            .send_messages_and_wait_commit(msgs)
            .map_err(LinkError::relayer)?;

        info!(
            "[Sync->{}] result {}",
            target.id(),
            PrettyEvents(tx_events.as_slice())
        );

        let ev = tx_events
            .clone()
            .into_iter()
            .find(|event_with_height| matches!(event_with_height.event, IbcEvent::ChainError(_)));

        match ev {
            Some(ev) => Err(LinkError::send(ev.event)),
            None => Ok(RelaySummary::from_events(
                tx_events
                    .into_iter()
                    .map(|event_with_height| event_with_height.event)
                    .collect(),
            )),
        }
    }
}

pub struct AsyncReply {
    pub responses: Vec<tx_sync::Response>,
}

impl SubmitReply for AsyncReply {
    fn empty() -> Self {
        Self { responses: vec![] }
    }

    fn len(&self) -> usize {
        self.responses.len()
    }
}

// TODO(Adi): Consider removing the senders and keep only a generic
//     send/submit method.
pub struct AsyncSender;

impl Submit for AsyncSender {
    type Reply = AsyncReply;

    fn submit(target: &impl ChainHandle, msgs: TrackedMsgs) -> Result<Self::Reply, LinkError> {
        let a = target
            .send_messages_and_wait_check_tx(msgs)
            .map_err(LinkError::relayer)?;
        let reply = AsyncReply { responses: a };

        // Note: There may be errors in the reply, for example:
        // `Response { code: Err(11), data: Data([]), log: Log("Too much gas wanted: 35000000, maximum is 25000000: out of gas")`
        // The runtime deliberately did not catch or retry on such errors.
        info!(target_chain = %target.id(), "{}", reply);

        Ok(reply)
    }
}

impl Display for AsyncReply {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "response(s): {}", self.responses.len())?;
        self.responses
            .iter()
            .try_for_each(|r| write!(f, "; {}:{}", PrettyCode(&r.code), r.hash))
    }
}
