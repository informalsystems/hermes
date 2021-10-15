use eyre::{eyre, Report as Error};
use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel;
use ibc_relayer::config::default;
use ibc_relayer::connection::Connection;
use ibc_relayer::foreign_client::ForeignClient;

#[derive(Debug)]
pub struct ChannelResult<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub channel: Channel<ChainA, ChainB>,
    pub channel_id_a: ChannelId,
    pub channel_id_b: ChannelId,
}

pub fn bootstrap_channel<ChainA: ChainHandle, ChainB: ChainHandle>(
    client_a_to_b: &ForeignClient<ChainA, ChainB>,
    client_b_to_a: &ForeignClient<ChainB, ChainA>,
    port_id_a: PortId,
    port_id_b: PortId,
) -> Result<ChannelResult<ChainA, ChainB>, Error> {
    let connection = Connection::new(
        client_a_to_b.clone(),
        client_b_to_a.clone(),
        default::connection_delay(),
    )?;

    let channel = Channel::new(connection, Order::Unordered, port_id_a, port_id_b, None)?;

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
        channel_id_a,
        channel_id_b,
    };

    Ok(res)
}
