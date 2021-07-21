use std::time::{Instant, Duration};

use crate::event::tx_hash::TxHash;
use crate::link::operational_data::OperationalData;
use crate::link::relay_sender::AsyncReply;
use crate::link::RelaySummary;
use crate::chain::handle::ChainHandle;
use ibc::query::{QueryTxRequest, QueryTxHash};

const TIMEOUT: Duration = Duration::from_secs(100);

#[derive(Clone)]
pub struct Unconfirmed {
    original_od: OperationalData,
    tx_hashes: Vec<TxHash>,
    submit_time: Instant,
    target_chain: Box<dyn ChainHandle>,
}

pub enum Outcome {
    TimedOut(OperationalData),
    Confirmed(RelaySummary),
    None
}

/// The mediator stores all unconfirmed data
/// and tries to confirm them asynchronously.
#[derive(Default)]
pub struct Mediator {
    pub list: Vec<Unconfirmed>
}

impl Mediator {
    pub fn insert(&mut self, r: AsyncReply, od: OperationalData, target: &Box<dyn ChainHandle>) {
        let u = Unconfirmed {
            original_od: od,
            tx_hashes: r.hashes().into(),
            submit_time: Instant::now(),
            target_chain: target.clone(),
        };
        self.list.push(u);
    }

    pub fn confirm_step(&mut self) -> Outcome {
        if let Some(u) = self.list.pop() {
            self.do_confirm(u);
        }

        Outcome::None
    }

    fn do_confirm(&mut self, u: Unconfirmed) {
        for hash in u.tx_hashes {
            if let Ok(events_per_tx) =
                u.target_chain.query_txs(QueryTxRequest::Transaction(QueryTxHash(hash.into())))
            {
                if !events_per_tx.is_empty() {
                    todo!()
                }
            }

        }
        todo!()
    }
}