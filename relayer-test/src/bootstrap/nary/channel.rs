use core::convert::TryInto;
use eyre::{eyre, Report as Error};
use ibc::core::ics04_channel::channel::Order;
use ibc::core::ics24_host::identifier::{PortChannelId, PortId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel;
use ibc_relayer::config::default;
use ibc_relayer::connection::Connection;
use ibc_relayer::foreign_client::ForeignClient;

use crate::types::nary::channel::ConnectedChannels;

pub fn bootstrap_channels<Handle: ChainHandle, const SIZE: usize>(
    foreign_clients: &[[ForeignClient<Handle, Handle>; SIZE]; SIZE],
    ports: &[[PortId; SIZE]; SIZE],
) -> Result<ConnectedChannels<Handle, SIZE>, Error> {
    let mut channels: Vec<[Channel<Handle, Handle>; SIZE]> = Vec::new();
    let mut port_channel_ids: Vec<[PortChannelId; SIZE]> = Vec::new();

    for (i, foreign_clients_b) in foreign_clients.iter().enumerate() {
        let mut channels_b: Vec<Channel<Handle, Handle>> = Vec::new();
        let mut port_channel_ids_b: Vec<PortChannelId> = Vec::new();

        for (j, foreign_client) in foreign_clients_b.iter().enumerate() {
            if i <= j {
                let counter_foreign_client = foreign_clients
                    .get(j)
                    .ok_or_else(|| eyre!("expected to get counter foreign client at {}/{}", j, i))?
                    .get(i)
                    .ok_or_else(|| {
                        eyre!("expected to get counter foreign client at {}/{}", j, i)
                    })?;

                let connection = Connection::new(
                    foreign_client.clone(),
                    counter_foreign_client.clone(),
                    default::connection_delay(),
                )?;

                let port_a = ports
                    .get(i)
                    .ok_or_else(|| eyre!("expected to get port at {}/{}", i, j))?
                    .get(j)
                    .ok_or_else(|| eyre!("expected to get port at {}/{}", i, j))?;

                let port_b = ports
                    .get(j)
                    .ok_or_else(|| eyre!("expected to get counter port at {}/{}", j, i))?
                    .get(i)
                    .ok_or_else(|| eyre!("expected to get counter port at {}/{}", j, i))?;

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
                let counter_channel = channels
                    .get(j)
                    .ok_or_else(|| eyre!("expected to get counter foreign client at {}/{}", j, i))?
                    .get(i)
                    .ok_or_else(|| {
                        eyre!("expected to get counter foreign client at {}/{}", j, i)
                    })?;

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

        let channels_b_array: [Channel<Handle, Handle>; SIZE] = channels_b
            .try_into()
            .map_err(|_| eyre!("expected channels array to be of size {}", SIZE))?;

        let port_channel_ids_b_array: [PortChannelId; SIZE] = port_channel_ids_b
            .try_into()
            .map_err(|_| eyre!("expected port channel ids array to be of size {}", SIZE))?;

        channels.push(channels_b_array);
        port_channel_ids.push(port_channel_ids_b_array);
    }

    let channels: [[Channel<Handle, Handle>; SIZE]; SIZE] = channels
        .try_into()
        .map_err(|_| eyre!("expected channels array to be of size {}", SIZE))?;

    let port_channel_ids: [[PortChannelId; SIZE]; SIZE] = port_channel_ids
        .try_into()
        .map_err(|_| eyre!("expected port channel ids array to be of size {}", SIZE))?;

    Ok(ConnectedChannels {
        channels,
        port_channel_ids,
    })
}
