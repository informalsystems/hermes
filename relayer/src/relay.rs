use anomaly::BoxError;

use crate::chain::handle::ChainHandle;
use crate::channel::{Channel, ChannelConfig};
use crate::connection::{Connection, ConnectionConfig};
use crate::foreign_client::{ForeignClient, ForeignClientConfig};

pub(crate) const MAX_ITER: u32 = 10;

pub fn channel_relay(
    a_chain_handle: Box<dyn ChainHandle>,
    b_chain_handle: Box<dyn ChainHandle>,
    conn_cfg: ConnectionConfig,
    chan_cfg: ChannelConfig,
) -> Result<(), BoxError> {
    // Instantiate the foreign client on the source chain.
    let client_on_a = ForeignClient::new(
        a_chain_handle.clone(),
        b_chain_handle.clone(),
        ForeignClientConfig::new(conn_cfg.a_end().chain_id(), conn_cfg.a_end().client_id()),
    )?;

    // Instantiate the foreign client on the destination chain.
    let client_on_b = ForeignClient::new(
        b_chain_handle.clone(),
        a_chain_handle.clone(),
        ForeignClientConfig::new(conn_cfg.b_end().chain_id(), conn_cfg.b_end().client_id()),
    )?;

    // Setup the connection between the two chains
    let connection = Connection::new(client_on_a, client_on_b, conn_cfg)?;

    // Setup the channel over the connection
    let _channel = Channel::new(connection, chan_cfg)?;

    // TODO: Re-enable `link` module in `relayer/src/lib.rs`
    // let link = Link::new(
    //     a_chain_handle,
    //     b_chain_handle,
    //     client_on_src, // Actual dependecy
    //     channel,       // Semantic dependecy
    //     LinkConfig::new(todo!(), todo!(), todo!()),
    // )?;

    // link.run()?;

    Ok(())
}
