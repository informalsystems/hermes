use core::fmt::{Display, Error as FmtError, Formatter};

use crate::link::relay_sender::AsyncReply;

use tendermint::Hash as TxHash;

/// A collection of transaction hashes.
#[derive(Clone)]
pub struct TxHashes(pub Vec<TxHash>);

impl From<AsyncReply> for TxHashes {
    fn from(r: AsyncReply) -> Self {
        Self(r.responses.into_iter().map(|e| e.hash).collect())
    }
}

impl From<TxHashes> for Vec<TxHash> {
    fn from(hs: TxHashes) -> Self {
        hs.0
    }
}

impl Display for TxHashes {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "TxHashes: count={}", self.0.len())?;
        self.0.iter().try_for_each(|r| write!(f, "; {}", r))
    }
}
