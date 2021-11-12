use core::convert::TryInto;
use eyre::{eyre, Report as Error};
use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics24_host::identifier::{PortChannelId, PortId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel;
use ibc_relayer::config::default;
use ibc_relayer::connection::Connection;
use ibc_relayer::foreign_client::ForeignClient;

use crate::types::nary::channel::{ConnectedChannels, DynamicConnectedChannels};
use crate::util::array::{assert_same_dimension, into_nested_vec};

pub fn bootstrap_channels_dynamic<Handle: ChainHandle>(
    foreign_clients: &Vec<Vec<ForeignClient<Handle, Handle>>>,
    ports: &Vec<Vec<PortId>>,
) -> Result<DynamicConnectedChannels<Handle>, Error> {
    let size = foreign_clients.len();

    assert_same_dimension(size, &foreign_clients)?;
    assert_same_dimension(size, &ports)?;

    let mut channels: Vec<Vec<Channel<Handle, Handle>>> = Vec::new();
    let mut port_channel_ids: Vec<Vec<PortChannelId>> = Vec::new();

    for (i, foreign_clients_b) in foreign_clients.iter().enumerate() {
        let mut channels_b: Vec<Channel<Handle, Handle>> = Vec::new();
        let mut port_channel_ids_b: Vec<PortChannelId> = Vec::new();

        for (j, foreign_client) in foreign_clients_b.iter().enumerate() {
            if i <= j {
                let counter_foreign_client = &foreign_clients[j][i];

                let connection = Connection::new(
                    foreign_client.clone(),
                    counter_foreign_client.clone(),
                    default::connection_delay(),
                )?;

                let port_a = &ports[i][j];
                let port_b = &ports[j][i];

                let channel = Channel::new(
                    connection,
                    Order::Unordered,
                    port_a.clone(),
                    port_b.clone(),
                    None,
                )?;

                let channel_id_a = channel
                    .a_side
                    .channel_id()
                    .ok_or_else(|| eyre!("expect channel id"))?
                    .clone();

                channels_b.push(channel);
                port_channel_ids_b.push(PortChannelId::new(channel_id_a, port_a.clone()));
            } else {
                let counter_channel = &channels[j][i];

                let channel = counter_channel.clone().flipped();

                let channel_id_a = channel
                    .a_side
                    .channel_id()
                    .ok_or_else(|| eyre!("expect channel id"))?
                    .clone();

                let port_a = channel.a_side.port_id().clone();

                channels_b.push(channel);
                port_channel_ids_b.push(PortChannelId::new(channel_id_a, port_a));
            }
        }

        channels.push(channels_b);
        port_channel_ids.push(port_channel_ids_b);
    }

    Ok(DynamicConnectedChannels {
        channels,
        port_channel_ids,
    })
}

pub fn bootstrap_channels<Handle: ChainHandle, const SIZE: usize>(
    foreign_clients: [[ForeignClient<Handle, Handle>; SIZE]; SIZE],
    ports: [[PortId; SIZE]; SIZE],
) -> Result<ConnectedChannels<Handle, SIZE>, Error> {
    let channels =
        bootstrap_channels_dynamic(&into_nested_vec(foreign_clients), &into_nested_vec(ports))?;

    Ok(channels.try_into()?)
}
