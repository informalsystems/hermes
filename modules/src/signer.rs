use crate::prelude::*;
use derive_more::{AsRef, Display, From, FromStr};
use serde::{Deserialize, Serialize};

#[derive(
    Clone,
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Serialize,
    Deserialize,
    Display,
    AsRef,
    FromStr,
    From,
)]
pub struct Signer(String);

impl Signer {
    pub fn new(s: impl ToString) -> Self {
        Self(s.to_string())
    }
}
