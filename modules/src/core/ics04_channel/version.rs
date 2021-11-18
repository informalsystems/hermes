use serde_derive::{Deserialize, Serialize};
use tendermint_proto::Protobuf;

use crate::core::ics04_channel::error::Error;
use crate::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct Version(String);

impl Protobuf<String> for Version {}

impl TryFrom<String> for Version {
    type Error = Error;
    fn try_from(value: String) -> Result<Self, Self::Error> {
        Ok(Version(value))
    }
}

impl From<Version> for String {
    fn from(domain_version: Version) -> Self {
        domain_version.0
    }
}

impl Default for Version {
    fn default() -> Self {
        Version("".to_string())
    }
}
