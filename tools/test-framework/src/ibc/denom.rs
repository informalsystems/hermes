/*!
   Helper functions for deriving IBC denom.
*/

use core::fmt::{self, Display};
use eyre::Report as Error;
use ibc::applications::ics20_fungible_token_transfer as token_transfer;

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
   A tagged version of [`derive_ibc_denom`](token_transfer::derive_ibc_denom)
   from the [`ibc`] module.

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
    match denom.value() {
        Denom::Base(denom) => {
            let hashed =
                token_transfer::derive_ibc_denom(port_id.value(), channel_id.value(), denom)?;

            Ok(MonoTagged::new(Denom::Ibc {
                path: format!("{}/{}", port_id, channel_id),
                denom: denom.clone(),
                hashed,
            }))
        }
        Denom::Ibc { path, denom, .. } => {
            let new_path = format!("{}/{}/{}", port_id, channel_id, path);
            let hashed =
                token_transfer::derive_ibc_denom_with_path(&format!("{}/{}", new_path, denom))?;

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
                write!(f, "{}", denom)
            }
            Denom::Ibc { hashed, .. } => {
                write!(f, "{}", hashed)
            }
        }
    }
}
