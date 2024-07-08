/*!
   Functions for bootstrapping N-ary number of channels.
*/

use core::time::Duration;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_types::core::ics04_channel::channel::Ordering;
use ibc_relayer_types::core::ics24_host::identifier::PortId;

use crate::bootstrap::binary::channel::{
    bootstrap_channel_with_connection, BootstrapChannelOptions,
};
use crate::bootstrap::nary::connection::bootstrap_connections_dynamic;
use crate::error::{handle_generic_error, Error};
use crate::types::binary::channel::ConnectedChannel;
use crate::types::nary::chains::{DynamicConnectedChains, NaryConnectedChains};
use crate::types::nary::channel::{ConnectedChannels, DynamicConnectedChannels};
use crate::types::nary::connection::{ConnectedConnections, DynamicConnectedConnections};
use crate::types::tagged::*;
use crate::util::array::into_nested_vec;
use crate::util::two_dim_hash_map::TwoDimMap;

/**
   Bootstrap a dynamic number of channels based on the number of
   connections in `DynamicConnectedConnections`.
   See [`crate::types::topology`] for more information.
*/
pub fn bootstrap_channels_with_connections_dynamic<Handle: ChainHandle>(
    connections: DynamicConnectedConnections<Handle>,
    ports: &Vec<Vec<PortId>>,
    order: Ordering,
    bootstrap_with_random_ids: bool,
) -> Result<DynamicConnectedChannels<Handle>, Error> {
    let mut channels: TwoDimMap<ConnectedChannel<Handle, Handle>> = TwoDimMap::new();

    for (src_chain, dst_chain, connection) in connections.connections().iter() {
        let channel = if let Some(counterparty_channel) = channels.get((dst_chain, src_chain)) {
            counterparty_channel.clone().flip()
        } else {
            // No channel is found, will create one
            let chain_a = &connection.connection.a_chain();
            let chain_b = &connection.connection.b_chain();
            let port_a = ports[src_chain][dst_chain].clone();
            let port_b = ports[dst_chain][src_chain].clone();

            let bootstrap_options = BootstrapChannelOptions::default()
                .order(order)
                .bootstrap_with_random_ids(bootstrap_with_random_ids);

            bootstrap_channel_with_connection(
                chain_a,
                chain_b,
                connection.clone(),
                &DualTagged::new(&port_a),
                &DualTagged::new(&port_b),
                bootstrap_options,
            )?
        };
        channels.insert((src_chain, dst_chain), channel);
    }

    Ok(DynamicConnectedChannels::new(channels))
}

/**
   Bootstrap a fixed number of connections with the same `SIZE`
   as in `ConnectedConnections`.
*/
pub fn bootstrap_channels_with_connections<Handle: ChainHandle, const SIZE: usize>(
    connections: ConnectedConnections<Handle, SIZE>,
    ports: [[PortId; SIZE]; SIZE],
    order: Ordering,
    bootstrap_with_random_ids: bool,
) -> Result<ConnectedChannels<Handle, SIZE>, Error> {
    let channels = bootstrap_channels_with_connections_dynamic(
        connections.into(),
        &into_nested_vec(ports),
        order,
        bootstrap_with_random_ids,
    )?;

    channels.try_into().map_err(handle_generic_error)
}

/**
   Bootstrap a dynamic number of channels together with the
   underlying connections based on the number of chain handles
   in `DynamicConnectedChains`.
*/
pub fn bootstrap_channels_and_connections_dynamic<Handle: ChainHandle>(
    chains: &DynamicConnectedChains<Handle>,
    ports: &Vec<Vec<PortId>>,
    connection_delay: Duration,
    order: Ordering,
    bootstrap_with_random_ids: bool,
) -> Result<DynamicConnectedChannels<Handle>, Error> {
    let connections = bootstrap_connections_dynamic(
        chains.foreign_clients(),
        connection_delay,
        bootstrap_with_random_ids,
    )?;

    bootstrap_channels_with_connections_dynamic(
        connections,
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
    order: Ordering,
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
