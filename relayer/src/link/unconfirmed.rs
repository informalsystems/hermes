use std::collections::VecDeque;
use std::iter::Iterator;
use std::time::{Duration, Instant};

use tracing::{debug, error, trace};

use ibc::events::IbcEvent;
use ibc::ics24_host::identifier::ChainId;
use ibc::query::{QueryTxHash, QueryTxRequest};

use crate::error::Error as RelayerError;
use crate::link::error::LinkError;
use crate::{
    chain::handle::ChainHandle,
    link::{operational_data::OperationalData, relay_sender::AsyncReply, RelaySummary, TxHashes},
};

pub const TIMEOUT: Duration = Duration::from_secs(100);
pub const MIN_BACKOFF: Duration = Duration::from_secs(1);

/// A wrapper over an [`OperationalData`] that is unconfirmed.
/// Additionally holds all the necessary information
/// to query for confirmations:
///     - hashes for all transactions in that op. data,
///     - the target chain to query for confirmations,
///     - timestamp to track time-outs and declare an
///         operational data as unconfirmed.
#[derive(Clone)]
pub struct Unconfirmed {
    pub original_od: OperationalData,
    pub tx_hashes: TxHashes,
    pub submit_time: Instant,
}

/// The mediator stores all unconfirmed data
/// and tries to confirm them asynchronously.
pub struct Mediator<Chain> {
    pub chain: Chain,
    pub unconfirmed: VecDeque<Unconfirmed>,
}

impl<Chain> Mediator<Chain> {
    pub fn new(chain: Chain) -> Self {
        Self {
            chain,
            unconfirmed: VecDeque::new(),
        }
    }
}

/// Represents the outcome of a [`Mediator`]'s
/// attempt to confirm an operational data.
pub enum Outcome {
    TimedOut(Unconfirmed),
    Confirmed(RelaySummary),
    None,
}

impl<Chain: ChainHandle> Mediator<Chain> {
    pub fn chain_id(&self) -> ChainId {
        self.chain.id()
    }

    pub fn insert(&mut self, r: AsyncReply, od: OperationalData) {
        let u = Unconfirmed {
            original_od: od,
            tx_hashes: r.into(),
            submit_time: Instant::now(),
        };
        self.unconfirmed.push_back(u);
    }

    pub fn reinsert(&mut self, unconfirmed: Unconfirmed) {
        self.unconfirmed.push_back(unconfirmed)
    }

    fn check_tx_events(&self, tx_hashes: &TxHashes) -> Result<Option<Vec<IbcEvent>>, RelayerError> {
        let mut all_events = Vec::new();
        for hash in &tx_hashes.0 {
            let mut events = self
                .chain
                .query_txs(QueryTxRequest::Transaction(QueryTxHash(hash.clone())))?;

            if events.is_empty() {
                return Ok(None);
            } else {
                all_events.append(&mut events)
            }
        }
        Ok(Some(all_events))
    }

    pub fn process_unconfirmed(
        &mut self,
        min_backoff: Duration,
        timeout: Duration,
        // resubmit: impl FnOnce(OperationalData) -> Result<(), LinkError>,
    ) -> Result<Outcome, LinkError> {
        if let Some(unconfirmed) = self.unconfirmed.pop_front() {
            let tx_hashes = &unconfirmed.tx_hashes;
            let submit_time = &unconfirmed.submit_time;

            // Elapsed time should fulfil some basic minimum so that
            // the relayer does not confirm too aggressively
            if unconfirmed.submit_time.elapsed() < min_backoff {
                self.unconfirmed.push_front(unconfirmed);
                Ok(Outcome::None)
            } else if submit_time.elapsed() > timeout {
                // This operational data should be re-submitted
                error!(
                    "[mediator->{}] timed out while confirming {}",
                    self.chain.id(),
                    tx_hashes
                );

                Ok(Outcome::TimedOut(unconfirmed))
            } else {
                trace!(
                    "[mediator] total unconfirmed left: {}",
                    self.unconfirmed.len()
                );

                trace!(
                    "[mediator->{}] trying to confirm {} ",
                    self.chain.id(),
                    tx_hashes
                );

                let events_result = self.check_tx_events(tx_hashes);
                match events_result {
                    Ok(None) => {
                        self.unconfirmed.push_back(unconfirmed);
                        Ok(Outcome::None)
                    }
                    Ok(Some(events)) => {
                        debug!(
                            "[mediator->{}] confirmed after {:#?}: {} ",
                            self.chain.id(),
                            unconfirmed.submit_time.elapsed(),
                            tx_hashes
                        );

                        let summary = RelaySummary::from_events(events);
                        return Ok(Outcome::Confirmed(summary));
                    }
                    Err(e) => {
                        error!(
                            "[mediator->{}] error querying for tx hashes {}: {}. will retry again later",
                            self.chain_id(),
                            tx_hashes,
                            e
                        );

                        self.unconfirmed.push_back(unconfirmed);

                        Err(LinkError::relayer(e))
                    }
                }
            }
        } else {
            Ok(Outcome::None)
        }
    }
}
