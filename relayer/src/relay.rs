use anomaly::BoxError;

use crate::chain::handle::ChainHandle;
use crate::connection::{ConnectionConfig, Connection};
use crate::channel::{ChannelConfig, Channel};
use crate::foreign_client::{ForeignClient, ForeignClientConfig};

pub fn channel_relay(src_chain_handle: impl ChainHandle, dst_chain_handle: impl ChainHandle, conn_cfg: ConnectionConfig, chan_cfg: ChannelConfig
) -> Result<(), BoxError> {

    // Instantiate the foreign client on the source chain.
    let client_on_src = ForeignClient::new(
        src_chain_handle.clone(),
        dst_chain_handle.clone(),
        ForeignClientConfig::new(conn_cfg.src_config.chain_id(), conn_cfg.src_config.client_id())
        )?;

    // Instantiate the foreign client on the destination chain.
    let client_on_dst = ForeignClient::new(
        dst_chain_handle.clone(),
        src_chain_handle.clone(),
        ForeignClientConfig::new(conn_cfg.dst_config.chain_id(), conn_cfg.dst_config.client_id())
    )?;

    // Setup the connection between the two chains
    let connection = Connection::new(
        src_chain_handle.clone(),
        dst_chain_handle.clone(),
        client_on_src, client_on_dst,
        conn_cfg,
    )?;

    // Setup the channel over the connection
    let _channel = Channel::new(
        src_chain_handle,
        dst_chain_handle,
        connection,
        chan_cfg,
    )?;

    // TODO: Re-enable `link` module in `relayer/src/lib.rs`
    // let link = Link::new(
    //     src_chain_handle,
    //     dst_chain_handle,
    //     client_on_src, // Actual dependecy
    //     channel,       // Semantic dependecy
    //     LinkConfig::new(todo!(), todo!(), todo!()),
    // )?;

    // link.run()?;

    Ok(())
}