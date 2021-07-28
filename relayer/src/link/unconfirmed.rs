use std::time::{Duration, Instant};

use tracing::{debug, error, trace};

use ibc::events::IbcEvent;
use ibc::query::{QueryTxHash, QueryTxRequest};

use crate::{
    chain::handle::ChainHandle,
    link::{operational_data::OperationalData, relay_sender::AsyncReply, RelaySummary, TxHashes},
};

use tendermint::abci::transaction;

const TIMEOUT: Duration = Duration::from_secs(100);

/// A wrapper over an [`OperationalData`] that is unconfirmed.
/// Additionally holds all the necessary information
/// to query for confirmations:
///     - hashes for all transactions in that op. data,
///     - the target chain to query for confirmations,
///     - timestamp to track time-outs and declare an
///         operational data as unconfirmed.
#[derive(Clone)]
pub struct Unconfirmed {
    original_od: OperationalData,
    tx_hashes: TxHashes,
    submit_time: Instant,
    target_chain: Box<dyn ChainHandle>,
}

/// The mediator stores all unconfirmed data
/// and tries to confirm them asynchronously.
#[derive(Default)]
pub struct Mediator {
    pub unconfirmed: Vec<Unconfirmed>,
}

/// Represents the outcome of a [`Mediator`]'s
/// attempt to confirm an operational data.
pub enum Outcome {
    TimedOut(OperationalData),
    Confirmed(RelaySummary),
    None,
}

/// [`Mediator`]'s internal representation of the outcome
/// of a single attempt to confirm an operational data.
enum DoConfirmOutcome {
    Unconfirmed(Unconfirmed),
    Confirmed(Unconfirmed, Vec<IbcEvent>),
}

impl Mediator {
    pub fn insert(&mut self, r: AsyncReply, od: OperationalData, target: Box<dyn ChainHandle>) {
        let u = Unconfirmed {
            original_od: od,
            tx_hashes: r.into(),
            submit_time: Instant::now(),
            target_chain: target,
        };
        self.unconfirmed.push(u);
    }

    pub fn confirm_step(&mut self) -> Outcome {
        if let Some(u) = self.unconfirmed.pop() {
            if u.submit_time.elapsed() > TIMEOUT {
                // This operational data should be re-submitted
                error!(
                    "[mediator->{}] timed out while confirming {}",
                    u.target_chain.id(),
                    u.tx_hashes
                );
                return Outcome::TimedOut(u.original_od);
            } else {
                trace!(
                    "[mediator->{}] trying to confirm {} ",
                    u.target_chain.id(),
                    u.tx_hashes
                );
                match self.do_confirm(u) {
                    DoConfirmOutcome::Unconfirmed(u) => {
                        trace!(
                            "[mediator->{}] unconfirmed, will retry agin later to confirm {} ",
                            u.target_chain.id(),
                            u.tx_hashes
                        );
                        self.unconfirmed.push(u);
                    }
                    DoConfirmOutcome::Confirmed(u, events) => {
                        debug!(
                            "[mediator->{}] confirmed after {:#?}: {} ",
                            u.target_chain.id(),
                            u.submit_time.elapsed(),
                            u.tx_hashes
                        );
                        let summary = RelaySummary::from_events(events);
                        return Outcome::Confirmed(summary);
                    }
                }
            }
        }

        Outcome::None
    }

    fn do_confirm(&self, u: Unconfirmed) -> DoConfirmOutcome {
        let mut events_accum = vec![];

        // Transform from `TxHash`es into `Hash`es
        let hashes: Vec<transaction::Hash> = u.tx_hashes.clone().into();

        for h in hashes {
            let query_events = u
                .target_chain
                .query_txs(QueryTxRequest::Transaction(QueryTxHash(h)));

            match query_events {
                Ok(mut events) => {
                    if !events.is_empty() {
                        events_accum.append(&mut events);
                    } else {
                        return DoConfirmOutcome::Unconfirmed(u);
                    }
                }
                Err(e) => {
                    // We retry later on
                    error!(
                        "[mediator->{}] error querying for tx hashes {}: {}",
                        u.target_chain.id(),
                        u.tx_hashes,
                        e
                    );
                    return DoConfirmOutcome::Unconfirmed(u);
                }
            }
        }

        DoConfirmOutcome::Confirmed(u, events_accum)
    }
}
