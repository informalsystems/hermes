use core::convert::TryInto;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;

use crate::bootstrap::binary::channel::bootstrap_channel_with_connection;
use crate::bootstrap::nary::connection::bootstrap_connections_dynamic;
use crate::error::{handle_generic_error, Error};
use crate::types::binary::channel::ConnectedChannel;
use crate::types::nary::chains::{ConnectedChains, DynamicConnectedChains};
use crate::types::nary::channel::{ConnectedChannels, DynamicConnectedChannels};
use crate::types::nary::connection::{ConnectedConnections, DynamicConnectedConnections};
use crate::types::tagged::*;
use crate::util::array::{assert_same_dimension, into_nested_vec};

pub fn bootstrap_channels_with_connections_dynamic<Handle: ChainHandle>(
    connections: DynamicConnectedConnections<Handle>,
    chains: &[Handle],
    ports: &[Vec<PortId>],
) -> Result<DynamicConnectedChannels<Handle>, Error> {
    let size = chains.len();

    assert_same_dimension(size, &connections.connections)?;
    assert_same_dimension(size, ports)?;

    let mut channels: Vec<Vec<ConnectedChannel<Handle, Handle>>> = Vec::new();

    for (i, connections_b) in connections.connections.into_iter().enumerate() {
        let mut channels_b: Vec<ConnectedChannel<Handle, Handle>> = Vec::new();

        for (j, connection) in connections_b.into_iter().enumerate() {
            if i <= j {
                let chain_a = &chains[i];
                let chain_b = &chains[j];

                let port_a = &ports[i][j];
                let port_b = &ports[j][i];

                let channel = bootstrap_channel_with_connection(
                    chain_a,
                    chain_b,
                    connection,
                    &DualTagged::new(port_a),
                    &DualTagged::new(port_b),
                    true,
                )?;

                channels_b.push(channel);
            } else {
                let counter_channel = &channels[j][i];
                let channel = counter_channel.clone().flip();

                channels_b.push(channel);
            }
        }

        channels.push(channels_b);
    }

    Ok(DynamicConnectedChannels { channels })
}

pub fn bootstrap_channels_with_connections<Handle: ChainHandle, const SIZE: usize>(
    connections: ConnectedConnections<Handle, SIZE>,
    chains: &[Handle; SIZE],
    ports: [[PortId; SIZE]; SIZE],
) -> Result<ConnectedChannels<Handle, SIZE>, Error> {
    let channels = bootstrap_channels_with_connections_dynamic(
        connections.into(),
        chains,
        &into_nested_vec(ports),
    )?;

    channels.try_into().map_err(handle_generic_error)
}

pub fn bootstrap_channels_dynamic<Handle: ChainHandle>(
    chains: &DynamicConnectedChains<Handle>,
    ports: &[Vec<PortId>],
) -> Result<DynamicConnectedChannels<Handle>, Error> {
    let connections = bootstrap_connections_dynamic(&chains.foreign_clients)?;

    bootstrap_channels_with_connections_dynamic(connections, &chains.chain_handles, ports)
}

pub fn bootstrap_channels<Handle: ChainHandle, const SIZE: usize>(
    chains: &ConnectedChains<Handle, SIZE>,
    ports: [[PortId; SIZE]; SIZE],
) -> Result<ConnectedChannels<Handle, SIZE>, Error> {
    let channels = bootstrap_channels_dynamic(&chains.clone().into(), &into_nested_vec(ports))?;

    channels.try_into()
}
