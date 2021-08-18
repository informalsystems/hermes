use core::fmt;
use std::iter::Iterator;
use std::time::{Duration, Instant};

use tracing::{debug, error, trace};

use ibc::events::IbcEvent;
use ibc::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::query::{QueryTxHash, QueryTxRequest};

use crate::error::Error as RelayerError;
use crate::link::error::LinkError;
use crate::util::queue::Queue;
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
pub struct UnconfirmedData {
    pub original_od: OperationalData,
    pub tx_hashes: TxHashes,
    pub submit_time: Instant,
}

/// The mediator stores all unconfirmed data
/// and tries to confirm them asynchronously.
pub struct PendingTxs<Chain> {
    pub chain: Chain,
    pub channel_id: ChannelId,
    pub port_id: PortId,
    pub counterparty_chain_id: ChainId,
    pub unconfirmed_queue: Queue<UnconfirmedData>,
}

impl<Chain> PendingTxs<Chain> {
    pub fn new(
        chain: Chain,
        channel_id: ChannelId,
        port_id: PortId,
        counterparty_chain_id: ChainId,
    ) -> Self {
        Self {
            chain,
            channel_id,
            port_id,
            counterparty_chain_id,
            unconfirmed_queue: Queue::new(),
        }
    }
}

impl<Chain: ChainHandle> PendingTxs<Chain> {
    pub fn chain_id(&self) -> ChainId {
        self.chain.id()
    }

    // Insert new unconfirmed transaction to the back of the queue.
    pub fn insert_new_pending_tx(&self, r: AsyncReply, od: OperationalData) {
        let u = UnconfirmedData {
            original_od: od,
            tx_hashes: r.into(),
            submit_time: Instant::now(),
        };
        self.unconfirmed_queue.push_back(u);
    }

    fn check_tx_events(&self, tx_hashes: &TxHashes) -> Result<Option<Vec<IbcEvent>>, RelayerError> {
        let mut all_events = Vec::new();
        for hash in &tx_hashes.0 {
            let mut events = self
                .chain
                .query_txs(QueryTxRequest::Transaction(QueryTxHash(*hash)))?;

            if events.is_empty() {
                return Ok(None);
            } else {
                all_events.append(&mut events)
            }
        }
        Ok(Some(all_events))
    }

    // Try and process one unconfirmed transaction if available.
    pub fn process_unconfirmed(
        &self,
        min_backoff: Duration,
        timeout: Duration,
        resubmit: impl FnOnce(OperationalData) -> Result<AsyncReply, LinkError>,
    ) -> Result<Option<RelaySummary>, LinkError> {
        // We process unconfirmed transactions in a FIFO manner, so take from
        // the front of the queue.
        if let Some(unconfirmed) = self.unconfirmed_queue.pop_front() {
            let tx_hashes = &unconfirmed.tx_hashes;
            let submit_time = &unconfirmed.submit_time;

            if unconfirmed.submit_time.elapsed() < min_backoff {
                // The transaction was only submitted recently.
                // We try not to reconfirm it too quickly as it may
                // have not yet committed to the chain.

                // Re-insert the unconfirmed transaction back to the
                // front of the queue so that it will be processed in
                // the next iteration.
                self.unconfirmed_queue.push_front(unconfirmed);
                Ok(None)
            } else {
                // Process the given unconfirmed transaction.

                trace!(
                    "[{}] total unconfirmed left: {}",
                    self,
                    self.unconfirmed_queue.len()
                );

                trace!("[{}] trying to confirm {} ", self, tx_hashes);

                // Check for TX events for the given unconfirmed transaction hashes.
                let events_result = self.check_tx_events(tx_hashes);
                match events_result {
                    Ok(None) => {
                        // There is no events for the associated transactions.
                        // This means the transaction has not yet been committed.

                        if submit_time.elapsed() > timeout {
                            // The submission time for the transaction has exceeded the
                            // timeout threshold. Returning Outcome::Timeout for the
                            // relayer to resubmit the transaction to the chain again.
                            error!("[{}] timed out while confirming {}", self, tx_hashes);

                            let resubmit_res = resubmit(unconfirmed.original_od.clone());

                            match resubmit_res {
                                Ok(reply) => {
                                    self.insert_new_pending_tx(reply, unconfirmed.original_od);
                                    Ok(None)
                                }
                                Err(e) => {
                                    self.unconfirmed_queue.push_back(unconfirmed);
                                    Err(e)
                                }
                            }
                        } else {
                            // Reinsert the unconfirmed transaction, this time
                            // to the back of the queue so that we process other
                            // unconfirmed transactions first in the meanwhile.
                            self.unconfirmed_queue.push_back(unconfirmed);
                            Ok(None)
                        }
                    }
                    Ok(Some(events)) => {
                        // We get a list of events for the transaction hashes,
                        // Meaning the transaction has been committed successfully
                        // to the chain.

                        debug!(
                            "[{}] confirmed after {:#?}: {} ",
                            self,
                            unconfirmed.submit_time.elapsed(),
                            tx_hashes
                        );

                        // Convert the events to RelaySummary and return them.
                        let summary = RelaySummary::from_events(events);
                        Ok(Some(summary))
                    }
                    Err(e) => {
                        // There are errors querying for the transaction hashes.
                        // This may be temporary errors when the relayer is communicating
                        // with the chain endpoint.

                        error!(
                            "[{}] error querying for tx hashes {}: {}. will retry again later",
                            self, tx_hashes, e
                        );

                        // Push it to the back of the unconfirmed queue to process it
                        // again at a later time.
                        self.unconfirmed_queue.push_back(unconfirmed);

                        Err(LinkError::relayer(e))
                    }
                }
            }
        } else {
            Ok(None)
        }
    }
}

impl<Chain: ChainHandle> fmt::Display for PendingTxs<Chain> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{}/{} -> {}",
            self.chain_id(),
            self.port_id,
            self.channel_id,
            self.counterparty_chain_id
        )
    }
}
