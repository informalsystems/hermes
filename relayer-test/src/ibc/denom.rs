/*!
   Helper functions for deriving IBC denom.
*/

use core::fmt::{self, Display};
use eyre::Report as Error;
use ibc::applications::ics20_fungible_token_transfer as token_transfer;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};

use crate::types::tagged::*;

/**
   A newtype wrapper to represent a denomination string.
*/
#[derive(Debug)]
pub struct Denom(pub String);

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
    port_id: &DualTagged<ChainB, ChainA, &PortId>,
    channel_id: &DualTagged<ChainB, ChainA, &ChannelId>,
    denom: &MonoTagged<ChainA, &Denom>,
) -> Result<MonoTagged<ChainB, Denom>, Error> {
    let res = token_transfer::derive_ibc_denom(
        port_id.value(),
        channel_id.value(),
        denom.value().0.as_str(),
    )?;

    Ok(MonoTagged::new(Denom(res)))
}

impl Display for Denom {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}
