use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::{Channel, ChannelSide};

use crate::error::Error;
use crate::types::binary::chains::ConnectedChains;
use crate::types::binary::connection::ConnectedConnection;

pub fn init_channel<ChainA: ChainHandle, ChainB: ChainHandle>(
    chains: &ConnectedChains<ChainA, ChainB>,
    connection: &ConnectedConnection<ChainA, ChainB>,
    src_port_id: PortId,
    dst_port_id: PortId,
) -> Result<Channel<ChainA, ChainB>, Error> {
    let channel = Channel {
        connection_delay: Default::default(),
        ordering: Order::Unordered,
        a_side: ChannelSide::new(
            chains.handle_a.clone(),
            connection.client.client_id_a.value().clone(),
            connection.connection_id_a.value().clone(),
            src_port_id,
            None,
        ),
        b_side: ChannelSide::new(
            chains.handle_b.clone(),
            connection.client.client_id_b.value().clone(),
            connection.connection_id_b.value().clone(),
            dst_port_id,
            None,
        ),
        version: None,
    };

    channel.build_chan_open_init_and_send()?;

    Ok(channel)
}
