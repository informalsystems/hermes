use eyre::Report as Error;
use ibc::applications::ics20_fungible_token_transfer as token_transfer;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};

use crate::tagged::*;

#[derive(Debug)]
pub struct Denom(pub String);

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
