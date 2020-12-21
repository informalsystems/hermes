use anomaly::BoxError;
use tracing::info;

use crate::chain::handle::ChainHandle;
use crate::channel::{Channel, ChannelConfig};
use crate::connection::{Connection, ConnectionConfig};
use crate::foreign_client::ForeignClient;
use crate::link::Link;

pub(crate) const MAX_ITER: u32 = 10;

pub fn channel_relay(
    a_chain_handle: Box<dyn ChainHandle>,
    b_chain_handle: Box<dyn ChainHandle>,
    conn_cfg: ConnectionConfig,
    chan_cfg: ChannelConfig,
) -> Result<(), BoxError> {
    info!("\nChannel Relay Loop\n");
    // Instantiate the foreign client on the source chain.
    let client_on_a = ForeignClient::new(a_chain_handle.clone(), b_chain_handle.clone())?;

    // Instantiate the foreign client on the destination chain.
    let client_on_b = ForeignClient::new(b_chain_handle.clone(), a_chain_handle.clone())?;

    // Setup the connection between the two chains
    let connection = Connection::new(client_on_a, client_on_b, conn_cfg)?;

    // Setup the channel over the connection
    let channel = Channel::new(connection, chan_cfg)?;

    let link = Link::new(channel);

    link.run()?;

    Ok(())
}
