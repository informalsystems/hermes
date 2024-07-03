/*!
   Helper functions for deriving IBC denom.
*/

use core::fmt::{self, Display};
use eyre::Report as Error;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};
use sha2::{Digest, Sha256};
use subtle_encoding::hex;

use crate::chain::chain_type::ChainType;
use crate::types::id::{TaggedChannelIdRef, TaggedPortIdRef};
use crate::types::tagged::*;

/**
   A newtype wrapper to represent a denomination string.
*/
#[derive(Debug, Clone)]
pub enum Denom {
    Base {
        display_name: String,
        raw_address: String,
    },
    Ibc {
        path: String,
        denom: Box<Denom>,
        hashed: String,
        token_denom: u8,
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
    chain_type: &ChainType,
    port_id: &TaggedPortIdRef<ChainB, ChainA>,
    channel_id: &TaggedChannelIdRef<ChainB, ChainA>,
    denom: &TaggedDenomRef<ChainA>,
) -> Result<TaggedDenom<ChainB>, Error> {
    match chain_type {
        ChainType::Namada => derive_namada_ibc_denom(port_id, channel_id, denom),
        _ => derive_cosmos_ibc_denom(port_id, channel_id, denom),
    }
}

fn derive_cosmos_ibc_denom<ChainA, ChainB>(
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
        Denom::Base { raw_address, .. } => {
            let hashed = derive_denom(port_id.value(), channel_id.value(), raw_address)?;

            Ok(MonoTagged::new(Denom::Ibc {
                path: format!("{port_id}/{channel_id}"),
                denom: Box::new((*denom.value()).clone()),
                hashed,
                token_denom: 0,
            }))
        }
        Denom::Ibc { path, denom, .. } => {
            let new_path = format!("{port_id}/{channel_id}/{path}");
            let hashed = derive_denom_with_path(&format!("{new_path}/{denom}"))?;

            Ok(MonoTagged::new(Denom::Ibc {
                path: new_path,
                denom: denom.clone(),
                hashed,
                token_denom: 0,
            }))
        }
    }
}

fn derive_namada_ibc_denom<ChainA, ChainB>(
    port_id: &TaggedPortIdRef<ChainB, ChainA>,
    channel_id: &TaggedChannelIdRef<ChainB, ChainA>,
    denom: &TaggedDenomRef<ChainA>,
) -> Result<TaggedDenom<ChainB>, Error> {
    match denom.value() {
        Denom::Base { raw_address, .. } => {
            let path = format!("{port_id}/{channel_id}");
            let ibc_token_addr = namada_ibc::trace::ibc_token(format!("{path}/{raw_address}"));

            Ok(MonoTagged::new(Denom::Ibc {
                path,
                denom: Box::new((*denom.value()).clone()),
                hashed: ibc_token_addr.to_string(),
                token_denom: 6,
            }))
        }
        Denom::Ibc { path, denom, .. } => {
            let new_path = format!("{port_id}/{channel_id}/{path}");
            let ibc_token_addr =
                namada_ibc::trace::ibc_token(format!("{new_path}/{}", denom.hash_only()));

            Ok(MonoTagged::new(Denom::Ibc {
                path: new_path,
                denom: denom.clone(),
                hashed: ibc_token_addr.to_string(),
                token_denom: 6,
            }))
        }
    }
}

impl Denom {
    pub fn base(display_name: &str, raw_address: &str) -> Self {
        Denom::Base {
            display_name: display_name.to_owned(),
            raw_address: raw_address.to_owned(),
        }
    }

    pub fn hash_only(&self) -> String {
        match self {
            Denom::Base { raw_address, .. } => raw_address.to_string(),
            Denom::Ibc { hashed, .. } => match hashed.find('/') {
                Some(index) => hashed[index + 1..].to_string(),
                None => hashed.to_string(),
            },
        }
    }

    pub fn display_name(&self) -> String {
        match self {
            Denom::Base { display_name, .. } => display_name.to_string(),
            Denom::Ibc { hashed, .. } => hashed.to_string(),
        }
    }

    pub fn namada_display_name(&self) -> String {
        match self {
            Denom::Base { display_name, .. } => display_name.to_string(),
            Denom::Ibc { path, denom, .. } => format!("{path}/{}", denom.namada_display_name()),
        }
    }

    pub fn as_str(&self) -> &str {
        match self {
            Denom::Base { display_name, .. } => display_name,
            Denom::Ibc { hashed, .. } => hashed,
        }
    }
}

impl Display for Denom {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Denom::Base { display_name, .. } => {
                write!(f, "{display_name}")
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
            (
                Self::Base {
                    display_name: d1,
                    raw_address: a1,
                },
                Self::Base {
                    display_name: d2,
                    raw_address: a2,
                },
            ) => (d1 == d2) && (a1 == a2),
            (
                Self::Ibc {
                    path: p1,
                    denom: d1,
                    hashed: h1,
                    token_denom: td1,
                },
                Self::Ibc {
                    path: p2,
                    denom: d2,
                    hashed: h2,
                    token_denom: td2,
                },
            ) => p1 == p2 && d1 == d2 && h1 == h2 && (td1 == td2),
            _ => self.as_str() == other.as_str(),
        }
    }
}

impl Eq for Denom {}
