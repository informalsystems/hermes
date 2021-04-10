use anomaly::BoxError;
use tracing::info;

use ibc::ics04_channel::channel::Order;

use crate::chain::handle::ChainHandle;
use crate::channel::Channel;
use crate::config::RelayPath;
use crate::connection::Connection;
use crate::foreign_client::ForeignClient;
use crate::link::{Link, LinkParameters};

pub(crate) const MAX_ITER: u32 = 10;

/// Used by the `hermes start ibc-0 ibc-1`
pub fn relay_on_new_link(
    a_chain_handle: Box<dyn ChainHandle>,
    b_chain_handle: Box<dyn ChainHandle>,
    delay: u64,
    ordering: Order,
    path: RelayPath,
) -> Result<(), BoxError> {
    // Setup the clients, connection and channel
    let channel = connect_with_new_channel(a_chain_handle, b_chain_handle, delay, ordering, path)?;

    let mut link = Link::new(channel);
    link.relay()?;

    Ok(())
}

/// Relays packets over a specified channel
/// Used by the `hermes start ibc-0 ibc-1 --src-port-id transfer --src-channel-id channel-0`
pub fn channel_relay(
    a_chain: Box<dyn ChainHandle>,
    b_chain: Box<dyn ChainHandle>,
    opts: LinkParameters,
) -> Result<(), BoxError> {
    let mut link = Link::new_from_opts(a_chain, b_chain, opts)?;
    Ok(link.relay()?)
}

/// Connects two ports of two chains creating new clients, connection and channel
/// Used by the `hermes channel handshake ibc-0 ibc-1`
pub fn connect_with_new_channel(
    a_chain_handle: Box<dyn ChainHandle>,
    b_chain_handle: Box<dyn ChainHandle>,
    delay: u64,
    ordering: Order,
    path: RelayPath,
) -> Result<Channel, BoxError> {
    info!("\nChannel Relay Loop\n");

    // Instantiate the foreign client on the two chains
    let client_on_a = ForeignClient::new(a_chain_handle.clone(), b_chain_handle.clone())?;
    let client_on_b = ForeignClient::new(b_chain_handle.clone(), a_chain_handle.clone())?;

    // Setup the connection between the two chains
    let connection = Connection::new(client_on_a, client_on_b, delay)?;

    // Setup the channel over the connection
    Ok(Channel::new(
        connection,
        ordering,
        path.a_port,
        path.b_port,
    )?)
}
