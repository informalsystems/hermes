use std::fmt;

use prost_types::Any;
use tendermint_rpc::endpoint::broadcast::tx_sync;
use tracing::info;

use ibc::events::{IbcEvent, PrettyEvents};

use crate::chain::handle::ChainHandle;
use crate::event::tx_hash::TxHash;
use crate::link::error::LinkError;
use crate::link::RelaySummary;

pub trait SubmitReply {
    fn empty() -> Self;
}

impl SubmitReply for RelaySummary {
    fn empty() -> Self {
        RelaySummary::empty()
    }
}

pub trait Submit {
    type Reply: SubmitReply;

    fn submit(target: &dyn ChainHandle, msgs: Vec<Any>) -> Result<Self::Reply, LinkError>;
}

pub struct SyncSender;

impl Submit for SyncSender {
    type Reply = RelaySummary;

    fn submit(target: &dyn ChainHandle, msgs: Vec<Any>) -> Result<Self::Reply, LinkError> {
        let tx_events = target.send_msgs(msgs)?;
        info!(
            "[Sync->{}] result {}\n",
            target.id(),
            PrettyEvents(&tx_events)
        );

        let ev = tx_events
            .clone()
            .into_iter()
            .find(|event| matches!(event, IbcEvent::ChainError(_)));

        match ev {
            Some(ev) => Err(LinkError::SendError(Box::new(ev))),
            None => Ok(RelaySummary::from_events(tx_events)),
        }
    }
}

pub struct AsyncReply {
    responses: Vec<tx_sync::Response>,
}

impl SubmitReply for AsyncReply {
    fn empty() -> Self {
        Self { responses: vec![] }
    }
}

impl AsyncReply {
    pub fn extend(&mut self, other: AsyncReply) {
        self.responses.extend(other.responses)
    }

    pub fn hashes(self) -> impl Iterator<Item = TxHash> {
        self.responses.into_iter().map(|r| r.hash.into())
    }
}

pub struct AsyncSender;

impl Submit for AsyncSender {
    type Reply = AsyncReply;

    fn submit(target: &dyn ChainHandle, msgs: Vec<Any>) -> Result<Self::Reply, LinkError> {
        let a = target.submit_msgs(msgs)?;
        let reply = AsyncReply { responses: a };
        info!("[Async~>{}] {}\n", target.id(), reply);

        Ok(reply)
    }
}

impl fmt::Display for AsyncReply {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "response(s): {}", self.responses.len())?;
        self.responses
            .iter()
            .try_for_each(|r| write!(f, "; {:?}:{}", r.code, r.hash))
    }
}
