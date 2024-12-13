/*!
   Helper functions for deriving IBC denom.
*/

use core::fmt::{self, Display};
use eyre::Report as Error;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};
use sha2::{Digest, Sha256};
use subtle_encoding::hex;

use crate::types::id::{TaggedChannelIdRef, TaggedPortIdRef};
use crate::types::tagged::*;

/**
   A newtype wrapper to represent a denomination string.
*/
#[derive(Debug, Clone)]
pub enum Denom {
    Base(String),
    Ibc {
        path: String,
        denom: String,
        hashed: String,
    },
}

/**
   Type alias for [`Denom`] tagged with the chain it belongs to.
*/
pub type TaggedDenom<Chain> = MonoTagged<Chain, Denom>;

/**
   Type alias for [`&Denom`](Denom) tagged with the chain it belongs to.
*/
pub type TaggedDenomRef<'a, Chain> = MonoTagged<Chain, &'a Denom>;

/**
   Derives the denom on `ChainB` based on a denom on `ChainA` that has been
   transferred to `ChainB` via IBC.

   Accepts the following arguments:

   - A `PortId` on `ChainB` that corresponds to a channel connected
     to `ChainA`.

   - A `ChannelId` on `ChainB` that corresponds to a channel connected
     to `ChainA`.

   - The original denomination on `ChainA`.

   Returns the derived denomination on `ChainB`.
*/
pub fn derive_ibc_denom<ChainA, ChainB>(
    port_id: &TaggedPortIdRef<ChainB, ChainA>,
    channel_id: &TaggedChannelIdRef<ChainB, ChainA>,
    denom: &TaggedDenomRef<ChainA>,
) -> Result<TaggedDenom<ChainB>, Error> {
    fn derive_denom(
        port_id: &PortId,
        channel_id: &ChannelId,
        denom: &str,
    ) -> Result<String, Error> {
        let transfer_path = format!("{port_id}/{channel_id}/{denom}");
        derive_denom_with_path(&transfer_path)
    }

    /// Derive the transferred token denomination using
    /// <https://github.com/cosmos/ibc-go/blob/main/docs/architecture/adr-001-coin-source-tracing.md>
    fn derive_denom_with_path(transfer_path: &str) -> Result<String, Error> {
        let mut hasher = Sha256::new();
        hasher.update(transfer_path.as_bytes());

        let denom_bytes = hasher.finalize();
        let denom_hex = String::from_utf8(hex::encode_upper(denom_bytes))?;

        Ok(format!("ibc/{denom_hex}"))
    }

    match denom.value() {
        Denom::Base(denom) => {
            let hashed = derive_denom(port_id.value(), channel_id.value(), denom)?;

            Ok(MonoTagged::new(Denom::Ibc {
                path: format!("{port_id}/{channel_id}"),
                denom: denom.clone(),
                hashed,
            }))
        }
        Denom::Ibc { path, denom, .. } => {
            let new_path = format!("{port_id}/{channel_id}/{path}");
            let hashed = derive_denom_with_path(&format!("{new_path}/{denom}"))?;

            Ok(MonoTagged::new(Denom::Ibc {
                path: new_path,
                denom: denom.clone(),
                hashed,
            }))
        }
    }
}

impl Denom {
    pub fn base(denom: &str) -> Self {
        Denom::Base(denom.to_string())
    }

    pub fn hash_only(&self) -> String {
        match self {
            Denom::Base(denom) => denom.to_string(),
            Denom::Ibc { hashed, .. } => match hashed.find('/') {
                Some(index) => hashed[index + 1..].to_string(),
                None => hashed.to_string(),
            },
        }
    }

    pub fn as_str(&self) -> &str {
        match self {
            Denom::Base(denom) => denom,
            Denom::Ibc { hashed, .. } => hashed,
        }
    }
}

impl Display for Denom {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Denom::Base(denom) => {
                write!(f, "{denom}")
            }
            Denom::Ibc { hashed, .. } => {
                write!(f, "{hashed}")
            }
        }
    }
}

impl PartialEq for Denom {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Base(d1), Self::Base(d2)) => d1 == d2,
            (
                Self::Ibc {
                    path: p1,
                    denom: d1,
                    hashed: h1,
                },
                Self::Ibc {
                    path: p2,
                    denom: d2,
                    hashed: h2,
                },
            ) => p1 == p2 && d1 == d2 && h1 == h2,
            _ => self.as_str() == other.as_str(),
        }
    }
}

impl Eq for Denom {}
