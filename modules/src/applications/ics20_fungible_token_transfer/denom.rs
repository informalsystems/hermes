use sha2::{Digest, Sha256};
use subtle_encoding::hex;

use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::prelude::*;

use super::error::Error;

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
