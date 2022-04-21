use crate::prelude::*;
use derive_more::{Display, From, FromStr};
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
    FromStr,
    From,
)]
pub struct Signer(String);

impl Signer {
    pub fn new(s: impl ToString) -> Self {
        Self(s.to_string())
    }
}

impl AsRef<str> for Signer {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}
