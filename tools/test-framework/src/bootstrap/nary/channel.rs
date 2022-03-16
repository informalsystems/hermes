/*!
   Functions for bootstrapping N-ary number of chanels.
*/

use core::convert::TryInto;
use core::time::Duration;
use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics04_channel::Version;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;

use crate::bootstrap::binary::channel::bootstrap_channel_with_connection;
use crate::bootstrap::nary::connection::bootstrap_connections_dynamic;
use crate::error::{handle_generic_error, Error};
use crate::types::binary::channel::ConnectedChannel;
use crate::types::nary::chains::{DynamicConnectedChains, NaryConnectedChains};
use crate::types::nary::channel::{ConnectedChannels, DynamicConnectedChannels};
use crate::types::nary::connection::{ConnectedConnections, DynamicConnectedConnections};
use crate::types::tagged::*;
use crate::util::array::{assert_same_dimension, into_nested_vec};

/**
   Bootstrap a dynamic number of channels based on the number of
   connections in `DynamicConnectedConnections`.
*/
pub fn bootstrap_channels_with_connections_dynamic<Handle: ChainHandle>(
    connections: DynamicConnectedConnections<Handle>,
    chains: &Vec<Handle>,
    ports: &Vec<Vec<PortId>>,
    order: Order,
    bootstrap_with_random_ids: bool,
) -> Result<DynamicConnectedChannels<Handle>, Error> {
    let size = chains.len();

    assert_same_dimension(size, connections.connections())?;
    assert_same_dimension(size, ports)?;

    let mut channels: Vec<Vec<ConnectedChannel<Handle, Handle>>> = Vec::new();

    for (i, connections_b) in connections.connections().iter().enumerate() {
        let mut channels_b: Vec<ConnectedChannel<Handle, Handle>> = Vec::new();

        for (j, connection) in connections_b.iter().enumerate() {
            if i <= j {
                let chain_a = &chains[i];
                let chain_b = &chains[j];

                let port_a = &ports[i][j];
                let port_b = &ports[j][i];

                let channel = bootstrap_channel_with_connection(
                    chain_a,
                    chain_b,
                    connection.clone(),
                    &DualTagged::new(port_a),
                    &DualTagged::new(port_b),
                    order,
                    Version::ics20(),
                    bootstrap_with_random_ids,
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

    Ok(DynamicConnectedChannels::new(channels))
}

/**
   Bootstrap a fixed number of connections with the same `SIZE`
   as in `ConnectedConnections`.
*/
pub fn bootstrap_channels_with_connections<Handle: ChainHandle, const SIZE: usize>(
    connections: ConnectedConnections<Handle, SIZE>,
    chains: [Handle; SIZE],
    ports: [[PortId; SIZE]; SIZE],
    order: Order,
    bootstrap_with_random_ids: bool,
) -> Result<ConnectedChannels<Handle, SIZE>, Error> {
    let channels = bootstrap_channels_with_connections_dynamic(
        connections.into(),
        &chains.into(),
        &into_nested_vec(ports),
        order,
        bootstrap_with_random_ids,
    )?;

    channels.try_into().map_err(handle_generic_error)
}

/**
   Boostrap a dynamic number of channels together with the
   underlying connections based on the number of chain handles
   in `DynamicConnectedChains`.
*/
pub fn bootstrap_channels_and_connections_dynamic<Handle: ChainHandle>(
    chains: &DynamicConnectedChains<Handle>,
    ports: &Vec<Vec<PortId>>,
    connection_delay: Duration,
    order: Order,
    bootstrap_with_random_ids: bool,
) -> Result<DynamicConnectedChannels<Handle>, Error> {
    let connections = bootstrap_connections_dynamic(
        chains.foreign_clients(),
        connection_delay,
        bootstrap_with_random_ids,
    )?;

    bootstrap_channels_with_connections_dynamic(
        connections,
        chains.chain_handles(),
        ports,
        order,
        bootstrap_with_random_ids,
    )
}

/**
   Bootstrap a fixed number of channels as specified by `SIZE`,
   together with bootstrapping the underlying connections.
*/
pub fn bootstrap_channels_and_connections<Handle: ChainHandle, const SIZE: usize>(
    chains: &NaryConnectedChains<Handle, SIZE>,
    ports: [[PortId; SIZE]; SIZE],
    connection_delay: Duration,
    order: Order,
    bootstrap_with_random_ids: bool,
) -> Result<ConnectedChannels<Handle, SIZE>, Error> {
    let channels = bootstrap_channels_and_connections_dynamic(
        &chains.clone().into(),
        &into_nested_vec(ports),
        connection_delay,
        order,
        bootstrap_with_random_ids,
    )?;

    channels.try_into()
}
