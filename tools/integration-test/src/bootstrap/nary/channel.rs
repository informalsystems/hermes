use core::convert::TryInto;
use eyre::Report as Error;
use ibc::core::ics24_host::identifier::PortId;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use crate::bootstrap::binary::channel::bootstrap_channel;
use crate::types::binary::channel::ConnectedChannel;
use crate::types::nary::channel::{ConnectedChannels, DynamicConnectedChannels};
use crate::types::tagged::*;
use crate::util::array::{assert_same_dimension, into_nested_vec};

pub fn bootstrap_channels_dynamic<Handle: ChainHandle>(
    foreign_clients: &[Vec<ForeignClient<Handle, Handle>>],
    ports: &[Vec<PortId>],
) -> Result<DynamicConnectedChannels<Handle>, Error> {
    let size = foreign_clients.len();

    assert_same_dimension(size, foreign_clients)?;
    assert_same_dimension(size, ports)?;

    let mut channels: Vec<Vec<ConnectedChannel<Handle, Handle>>> = Vec::new();

    for (i, foreign_clients_b) in foreign_clients.iter().enumerate() {
        let mut channels_b: Vec<ConnectedChannel<Handle, Handle>> = Vec::new();

        for (j, foreign_client) in foreign_clients_b.iter().enumerate() {
            if i <= j {
                let counter_foreign_client = &foreign_clients[j][i];

                let port_a = &ports[i][j];
                let port_b = &ports[j][i];

                let channel = bootstrap_channel(
                    counter_foreign_client,
                    foreign_client,
                    &DualTagged::new(port_a),
                    &DualTagged::new(port_b),
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

    Ok(DynamicConnectedChannels { channels })
}

pub fn bootstrap_channels<Handle: ChainHandle, const SIZE: usize>(
    foreign_clients: [[ForeignClient<Handle, Handle>; SIZE]; SIZE],
    ports: [[PortId; SIZE]; SIZE],
) -> Result<ConnectedChannels<Handle, SIZE>, Error> {
    let channels =
        bootstrap_channels_dynamic(&into_nested_vec(foreign_clients), &into_nested_vec(ports))?;

    channels.try_into()
}
