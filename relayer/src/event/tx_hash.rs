use std::fmt;
use std::hash::{Hash, Hasher};
use std::str::FromStr;

use k256::elliptic_curve::bigint::subtle::ConstantTimeEq;
use tendermint::abci::transaction;

#[derive(Copy, Clone, Debug)]
pub struct TxHash {
    inner: transaction::Hash,
}

impl From<transaction::Hash> for TxHash {
    fn from(h: transaction::Hash) -> Self {
        Self { inner: h }
    }
}

impl From<TxHash> for transaction::Hash {
    fn from(h: TxHash) -> Self {
        h.inner
    }
}

impl PartialEq for TxHash {
    fn eq(&self, other: &Self) -> bool {
        self.inner.ct_eq(&other.inner).into()
    }
}

impl Eq for TxHash {}

impl Hash for TxHash {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

impl FromStr for TxHash {
    type Err = tendermint::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let hash: transaction::Hash = s.parse()?;
        Ok(Self { inner: hash })
    }
}

impl fmt::Display for TxHash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}
