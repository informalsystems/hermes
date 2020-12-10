use anomaly::BoxError;

use crate::chain::handle::ChainHandle;
use crate::channel::{Channel, ChannelConfig};
use crate::connection::{Connection, ConnectionConfig};
use crate::foreign_client::{ForeignClient, ForeignClientConfig};
use crate::link::Link;

pub(crate) const MAX_ITER: u32 = 10;

pub fn channel_relay(
    a_chain_handle: impl ChainHandle,
    b_chain_handle: impl ChainHandle,
    conn_cfg: ConnectionConfig,
    chan_cfg: ChannelConfig,
) -> Result<(), BoxError> {
    // Instantiate the foreign client on the source chain.
    let client_on_a = ForeignClient::new(
        &a_chain_handle,
        &b_chain_handle,
        ForeignClientConfig::new(conn_cfg.a_end().chain_id(), conn_cfg.a_end().client_id()),
    )?;

    // Instantiate the foreign client on the destination chain.
    let client_on_b = ForeignClient::new(
        &b_chain_handle,
        &a_chain_handle,
        ForeignClientConfig::new(conn_cfg.b_end().chain_id(), conn_cfg.b_end().client_id()),
    )?;

    // Setup the connection between the two chains
    let connection = Connection::new(
        a_chain_handle.clone(),
        b_chain_handle.clone(),
        client_on_a,
        client_on_b,
        conn_cfg,
    )?;

    // Setup the channel over the connection
    let channel = Channel::new(
        a_chain_handle.clone(),
        b_chain_handle.clone(),
        connection,
        chan_cfg,
    )?;

    let link = Link::new(channel);

    link.run(a_chain_handle, b_chain_handle)?;

    Ok(())
}
