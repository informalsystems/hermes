/*!
    Helper functions for bootstrapping a channel between two chains.
*/

use eyre::{eyre, Report as Error};
use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::{Channel, ChannelSide};
use ibc_relayer::foreign_client::ForeignClient;
use tracing::{debug, info};

use super::connection::bootstrap_connection;
use crate::types::binary::chains::ConnectedChains;
use crate::types::binary::channel::ConnectedChannel;
use crate::types::binary::connection::ConnectedConnection;
use crate::types::id::TaggedPortIdRef;
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

/**
    Create a new [`ConnectedChannel`] between two chains using foreign clients
    with initialized client IDs.
*/
pub fn bootstrap_channel<ChainA: ChainHandle, ChainB: ChainHandle>(
    client_b_to_a: &ForeignClient<ChainA, ChainB>,
    client_a_to_b: &ForeignClient<ChainB, ChainA>,
    port_a: &TaggedPortIdRef<ChainA, ChainB>,
    port_b: &TaggedPortIdRef<ChainB, ChainA>,
) -> Result<ConnectedChannel<ChainA, ChainB>, Error> {
    let connection = bootstrap_connection(client_b_to_a, client_a_to_b)?;

    bootstrap_channel_with_connection(
        &client_a_to_b.src_chain(),
        &client_a_to_b.dst_chain(),
        connection,
        port_a,
        port_b,
    )
}

/**
   Create a new [`ConnectedChannel`] using existing [`ConnectedConnection`].
*/
pub fn bootstrap_channel_with_connection<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
    connection: ConnectedConnection<ChainA, ChainB>,
    port_a: &TaggedPortIdRef<ChainA, ChainB>,
    port_b: &TaggedPortIdRef<ChainB, ChainA>,
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
        "created new chain/client/connection/channel from {}/{}/{}/{} to {}/{}/{}/{}",
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

/**
   Create a random number of dummy channel IDs so that the bootstrapped
   channel ID is random instead of being always `channel-0`.

   This would help us catch bugs where the channel IDs are used at
   the wrong side of the chain, but still got accepted because the
   channel IDs on both sides are the same.
*/
pub fn pad_channel_id<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
    connection: &ConnectedConnection<ChainA, ChainB>,
    port_id: &TaggedPortIdRef<ChainA, ChainB>,
) -> Result<(), Error> {
    let client_id_a = &connection.client.client_id_a;
    let client_id_b = &connection.client.client_id_b;

    for i in 0..random_u64_range(1, 6) {
        debug!(
            "creating new channel id {} on chain/connection/client {}/{}/{}",
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
                None,
            ),
            b_side: ChannelSide::new(
                chain_a.clone(),
                client_id_a.value().clone(),
                connection.connection_id_a.value().clone(),
                port_id.cloned().into_value(),
                None,
                None,
            ),
            connection_delay: connection.connection.delay_period,
        };

        channel.build_chan_open_init_and_send()?;
    }

    Ok(())
}
