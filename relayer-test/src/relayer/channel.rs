use eyre::{eyre, Report as Error};
use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel;
use ibc_relayer::config::default;
use ibc_relayer::connection::Connection;
use ibc_relayer::foreign_client::ForeignClient;

use crate::tagged::dual::Tagged;

#[derive(Debug)]
pub struct ChannelResult<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub channel: Channel<ChainA, ChainB>,
    pub channel_id_a: Tagged<ChainB, ChainA, ChannelId>,
    pub channel_id_b: Tagged<ChainA, ChainB, ChannelId>,
}

pub fn bootstrap_channel<ChainA: ChainHandle, ChainB: ChainHandle>(
    client_a_to_b: &ForeignClient<ChainB, ChainA>,
    client_b_to_a: &ForeignClient<ChainA, ChainB>,
    port_id_a: &Tagged<ChainA, ChainB, PortId>,
    port_id_b: &Tagged<ChainB, ChainA, PortId>,
) -> Result<ChannelResult<ChainB, ChainA>, Error> {
    let connection = Connection::new(
        client_a_to_b.clone(),
        client_b_to_a.clone(),
        default::connection_delay(),
    )?;

    let channel = Channel::new(
        connection,
        Order::Unordered,
        port_id_a.value().clone(),
        port_id_b.value().clone(),
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

    let res = ChannelResult {
        channel,
        channel_id_a: Tagged::new(channel_id_a),
        channel_id_b: Tagged::new(channel_id_b),
    };

    Ok(res)
}
