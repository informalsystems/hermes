/*!
    Helper functions for bootstrapping a channel with full handshake already
    established between two chains.
*/

use eyre::{eyre, Report as Error};
use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics24_host::identifier::PortId;
use ibc::timestamp::ZERO_DURATION;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::{Channel, ChannelSide};
use ibc_relayer::config::default;
use ibc_relayer::connection::{Connection, ConnectionSide};
use ibc_relayer::foreign_client::ForeignClient;
use tracing::info;

use crate::relayer::connection::TaggedConnectionExt;
use crate::relayer::foreign_client::TaggedForeignClientExt;
use crate::types::binary::chains::ConnectedChains;
use crate::types::binary::channel::ConnectedChannel;
use crate::types::binary::client::ConnectedClients;
use crate::types::binary::connection::ConnectedConnection;
use crate::types::id::{ClientIdRef, PortIdRef};
use crate::types::tagged::*;
use crate::util::random::random_u64_range;

/**
   Create a new [`ConnectedChannel`] based on the provided [`ConnectedChains`].

   Also accepts the [`PortId`] that should be used for the two sides of the
   channel.
*/
pub fn bootstrap_channel_with_chains<ChainA: ChainHandle, ChainB: ChainHandle>(
    chains: &ConnectedChains<ChainA, ChainB>,
    port_a: &PortId,
    port_b: &PortId,
) -> Result<ConnectedChannel<ChainA, ChainB>, Error> {
    let channel = bootstrap_channel(
        &chains.client_b_to_a,
        &chains.client_a_to_b,
        &DualTagged::new(port_a),
        &DualTagged::new(port_b),
    )?;

    Ok(channel)
}

pub fn bootstrap_connection<ChainA: ChainHandle, ChainB: ChainHandle>(
    client_b_to_a: &ForeignClient<ChainA, ChainB>,
    client_a_to_b: &ForeignClient<ChainB, ChainA>,
) -> Result<ConnectedConnection<ChainA, ChainB>, Error> {
    let chain_a = client_a_to_b.src_chain();
    let chain_b = client_a_to_b.dst_chain();

    let client_id_a = client_b_to_a.tagged_client_id();
    let client_id_b = client_a_to_b.tagged_client_id();

    pad_connection_id(&chain_a, &chain_b, &client_id_a, &client_id_b)?;

    pad_connection_id(&chain_b, &chain_a, &client_id_b, &client_id_a)?;

    let connection = Connection::new(
        client_b_to_a.clone(),
        client_a_to_b.clone(),
        default::connection_delay(),
    )?;

    let connection_id_a = connection
        .tagged_connection_id_a()
        .ok_or_else(|| eyre!("expected connection id to present"))?
        .cloned();

    let connection_id_b = connection
        .tagged_connection_id_b()
        .ok_or_else(|| eyre!("expected connection id to present"))?
        .cloned();

    info!(
        "created new connection from chain/client/connection {}/{}/{} to {}/{}/{}",
        chain_a.id(),
        client_id_a,
        connection_id_a,
        chain_b.id(),
        client_id_b,
        connection_id_b,
    );

    let connected_connection = ConnectedConnection {
        connection,

        client: ConnectedClients {
            client_id_a: client_id_a.cloned(),

            client_id_b: client_id_b.cloned(),
        },

        connection_id_a,

        connection_id_b,
    };

    Ok(connected_connection)
}

pub fn pad_connection_id<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
    client_id_a: &ClientIdRef<ChainA, ChainB>,
    client_id_b: &ClientIdRef<ChainB, ChainA>,
) -> Result<(), Error> {
    for i in 0..random_u64_range(1, 8) {
        info!(
            "creating new connection id {} on chain {}",
            i + 1,
            chain_a.id()
        );

        let connection: Connection<ChainB, ChainA> = Connection {
            delay_period: ZERO_DURATION,
            a_side: ConnectionSide::new(chain_b.clone(), client_id_b.cloned().into_value(), None),
            b_side: ConnectionSide::new(chain_a.clone(), client_id_a.cloned().into_value(), None),
        };

        connection.build_conn_init_and_send()?;
    }

    Ok(())
}

pub fn pad_channel_id<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
    connection: &ConnectedConnection<ChainA, ChainB>,
    port_id: &PortIdRef<ChainA, ChainB>,
) -> Result<(), Error> {
    let client_id_a = &connection.client.client_id_a;
    let client_id_b = &connection.client.client_id_b;

    for i in 0..random_u64_range(1, 8) {
        info!(
            "creating new connection id {} on chain/connection/client {}/{}/{}",
            i + 1,
            chain_a.id(),
            connection.connection_id_a,
            client_id_a,
        );

        let channel: Channel<ChainB, ChainA> = Channel {
            ordering: Order::Unordered,
            a_side: ChannelSide::new(
                chain_b.clone(),
                client_id_b.value().clone(),
                connection.connection_id_b.value().clone(),
                port_id.cloned().into_value(),
                None,
            ),
            b_side: ChannelSide::new(
                chain_a.clone(),
                client_id_a.value().clone(),
                connection.connection_id_a.value().clone(),
                port_id.cloned().into_value(),
                None,
            ),
            connection_delay: connection.connection.delay_period,
            version: None,
        };

        channel.build_chan_open_init_and_send()?;
    }

    Ok(())
}

/**
    Create a new connected channel between two chains using new IBC client
    and connection.

    TODO: Bootstrap the channels in such a way that the two channels
    have random-ish IDs. Since Cosmos SDK is generating the IDs sequentially,
    this would mean we have to create dummy client/connection/channel
    a random amount of times before we create the actual one that is
    going to be used.
*/
pub fn bootstrap_channel<ChainA: ChainHandle, ChainB: ChainHandle>(
    client_b_to_a: &ForeignClient<ChainA, ChainB>,
    client_a_to_b: &ForeignClient<ChainB, ChainA>,
    port_a: &PortIdRef<ChainA, ChainB>,
    port_b: &PortIdRef<ChainB, ChainA>,
) -> Result<ConnectedChannel<ChainA, ChainB>, Error> {
    let connection = bootstrap_connection(client_b_to_a, client_a_to_b)?;

    bootstrap_with_connection(
        &client_a_to_b.src_chain(),
        &client_a_to_b.dst_chain(),
        connection,
        port_a,
        port_b,
    )
}

pub fn bootstrap_with_connection<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
    connection: ConnectedConnection<ChainA, ChainB>,
    port_a: &PortIdRef<ChainA, ChainB>,
    port_b: &PortIdRef<ChainB, ChainA>,
) -> Result<ConnectedChannel<ChainA, ChainB>, Error> {
    pad_channel_id(chain_a, chain_b, &connection, port_a)?;
    pad_channel_id(chain_b, chain_a, &connection.clone().flip(), port_b)?;

    let channel = Channel::new(
        connection.connection.clone(),
        Order::Unordered,
        port_a.0.clone(),
        port_b.0.clone(),
        None,
    )?;

    let channel_id_a = channel
        .a_side
        .channel_id()
        .ok_or_else(|| eyre!("expect channel id"))?
        .clone();

    let channel_id_b = channel
        .b_side
        .channel_id()
        .ok_or_else(|| eyre!("expect channel id"))?
        .clone();

    info!(
        "created new channel chain/client/connection/channel from {}/{}/{}/{} to {}/{}/{}/{}",
        chain_a.id(),
        connection.client.client_id_a,
        connection.connection_id_a,
        channel_id_a,
        chain_b.id(),
        connection.client.client_id_b,
        connection.connection_id_b,
        channel_id_b,
    );

    let res = ConnectedChannel {
        connection,
        channel,
        channel_id_a: DualTagged::new(channel_id_a),
        channel_id_b: DualTagged::new(channel_id_b),
        port_a: port_a.cloned(),
        port_b: port_b.cloned(),
    };

    Ok(res)
}
