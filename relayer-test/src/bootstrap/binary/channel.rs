/*!
    Helper functions for bootstrapping a channel with full handshake already
    established between two chains.
*/

use eyre::{eyre, Report as Error};
use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel as BaseChannel;
use ibc_relayer::config::default;
use ibc_relayer::connection::Connection;
use ibc_relayer::foreign_client::ForeignClient;

use crate::types::binary::chains::ConnectedChains;
use crate::types::binary::channel::ConnectedChannel;
use crate::types::id::PortIdRef;
use crate::types::tagged::*;

/**
   Create a new connnected [`Channel`] based on the provided [`ConnectedChains`].

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
    let connection = Connection::new(
        client_b_to_a.clone(),
        client_a_to_b.clone(),
        default::connection_delay(),
    )?;

    let channel = BaseChannel::new(
        connection,
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

    let res = ConnectedChannel {
        channel,
        channel_id_a: DualTagged::new(channel_id_a),
        channel_id_b: DualTagged::new(channel_id_b),
        port_a: port_a.cloned(),
        port_b: port_b.cloned(),
    };

    Ok(res)
}
