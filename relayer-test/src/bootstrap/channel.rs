use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use tracing::info;

use crate::chain::builder::ChainBuilder;
use crate::error::Error;
use crate::relayer::channel::{bootstrap_channel, Channel};
use crate::tagged::*;

use super::deployment::ChainDeployment;
use super::pair::boostrap_chain_pair;

pub struct ChainChannelDeployment<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub chains: ChainDeployment<ChainA, ChainB>,
    pub channel: Channel<ChainA, ChainB>,
}

pub fn boostrap_chain_and_channel_pair(
    builder: &ChainBuilder,
    port: &PortId,
) -> Result<ChainChannelDeployment<impl ChainHandle, impl ChainHandle>, Error> {
    let chains = boostrap_chain_pair(&builder)?;

    let port_a = DualTagged::new(port);
    let port_b = DualTagged::new(port);

    let channel = bootstrap_channel(
        &chains.client_b_to_a,
        &chains.client_a_to_b,
        &port_a,
        &port_b,
    )?;

    info!("created new channel {:?}", channel);

    Ok(ChainChannelDeployment { chains, channel })
}
