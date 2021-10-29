use eyre::{eyre, Report as Error};
use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel as BaseChannel;
use ibc_relayer::config::default;
use ibc_relayer::connection::Connection;
use ibc_relayer::foreign_client::ForeignClient;

use crate::tagged::dual::Tagged;

#[derive(Debug)]
pub struct Channel<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub channel: BaseChannel<ChainA, ChainB>,
    pub channel_id_a: Tagged<ChainA, ChainB, ChannelId>,
    pub channel_id_b: Tagged<ChainB, ChainA, ChannelId>,
    pub port_a: Tagged<ChainA, ChainB, PortId>,
    pub port_b: Tagged<ChainB, ChainA, PortId>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> Channel<ChainA, ChainB> {
    pub fn flip(self) -> Channel<ChainB, ChainA> {
        Channel {
            channel: self.channel.flipped(),
            channel_id_a: self.channel_id_b,
            channel_id_b: self.channel_id_a,
            port_a: self.port_b,
            port_b: self.port_a,
        }
    }
}

// Create a new connected channel between chain A and B
// using new IBC client and connection.
pub fn bootstrap_channel<ChainA: ChainHandle, ChainB: ChainHandle>(
    client_b_to_a: &ForeignClient<ChainA, ChainB>,
    client_a_to_b: &ForeignClient<ChainB, ChainA>,
    port_a: &Tagged<ChainA, ChainB, &PortId>,
    port_b: &Tagged<ChainB, ChainA, &PortId>,
) -> Result<Channel<ChainA, ChainB>, Error> {
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

    let res = Channel {
        channel,
        channel_id_a: Tagged::new(channel_id_a),
        channel_id_b: Tagged::new(channel_id_b),
        port_a: port_a.cloned(),
        port_b: port_b.cloned(),
    };

    Ok(res)
}
