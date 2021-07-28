use std::fmt;

use tendermint::abci::transaction;

use crate::link::relay_sender::AsyncReply;

/// A collection of transaction hashes.
#[derive(Clone)]
pub struct TxHashes {
    inner: Vec<transaction::Hash>,
}

impl From<AsyncReply> for TxHashes {
    fn from(r: AsyncReply) -> Self {
        Self {
            inner: r.responses.into_iter().map(|e| e.hash).collect(),
        }
    }
}

impl From<TxHashes> for Vec<transaction::Hash> {
    fn from(hs: TxHashes) -> Self {
        hs.inner
    }
}

impl fmt::Display for TxHashes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TxHashes: count={}", self.inner.len())?;
        self.inner.iter().try_for_each(|r| write!(f, "; {}", r))
    }
}
