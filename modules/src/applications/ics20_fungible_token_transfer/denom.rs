use core::fmt;
use core::str::FromStr;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use subtle_encoding::hex;

use super::error::Error;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::prelude::*;

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Denom(String);

impl AsRef<str> for Denom {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

impl FromStr for Denom {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.trim().is_empty() {
            Err(Error::empty_base_denom())
        } else if s.contains('/') {
            Err(Error::invalid_base_denom())
        } else {
            Ok(Denom(s.to_owned()))
        }
    }
}

impl fmt::Display for Denom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub fn derive_ibc_denom(
    port_id: &PortId,
    channel_id: &ChannelId,
    denom: &str,
) -> Result<String, Error> {
    let transfer_path = format!("{}/{}/{}", port_id, channel_id, denom);
    derive_ibc_denom_with_path(&transfer_path)
}

/// Derive the transferred token denomination using
/// <https://github.com/cosmos/ibc-go/blob/main/docs/architecture/adr-001-coin-source-tracing.md>
pub fn derive_ibc_denom_with_path(transfer_path: &str) -> Result<String, Error> {
    let mut hasher = Sha256::new();
    hasher.update(transfer_path.as_bytes());

    let denom_bytes = hasher.finalize();
    let denom_hex = String::from_utf8(hex::encode_upper(denom_bytes)).map_err(Error::utf8)?;

    Ok(format!("ibc/{}", denom_hex))
}
