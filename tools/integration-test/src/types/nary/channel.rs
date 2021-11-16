use core::convert::TryFrom;
use eyre::eyre;
use ibc::core::ics24_host::identifier::{ChannelId, PortChannelId, PortId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel;
use ibc_relayer::connection::Connection;

use super::chains::TaggedHandle;
use crate::error::Error;
use crate::types::binary::channel::ConnectedChannel as BinaryConnectedChannel;
use crate::types::binary::client::ConnectedClients;
use crate::types::binary::connection::ConnectedConnection;
use crate::types::tagged::*;
use crate::util::array::try_into_nested_array;

#[derive(Debug, Clone)]
pub struct ConnectedChannels<Handle: ChainHandle, const SIZE: usize> {
    pub connections: [[Connection<Handle, Handle>; SIZE]; SIZE],
    pub channels: [[Channel<Handle, Handle>; SIZE]; SIZE],
    pub port_channel_ids: [[PortChannelId; SIZE]; SIZE],
}

#[derive(Debug, Clone)]
pub struct DynamicConnectedChannels<Handle: ChainHandle> {
    pub connections: Vec<Vec<Connection<Handle, Handle>>>,
    pub channels: Vec<Vec<Channel<Handle, Handle>>>,
    pub port_channel_ids: Vec<Vec<PortChannelId>>,
}

pub type TaggedChannel<Handle, const FIRST: usize, const SECOND: usize> =
    Channel<TaggedHandle<Handle, FIRST>, TaggedHandle<Handle, SECOND>>;

pub type TaggedChannelId<Handle, const FIRST: usize, const SECOND: usize> =
    DualTagged<TaggedHandle<Handle, FIRST>, TaggedHandle<Handle, SECOND>, ChannelId>;

pub type TaggedPortId<Handle, const FIRST: usize, const SECOND: usize> =
    DualTagged<TaggedHandle<Handle, FIRST>, TaggedHandle<Handle, SECOND>, PortId>;

pub type TaggedPortChannelId<Handle, const FIRST: usize, const SECOND: usize> =
    DualTagged<TaggedHandle<Handle, FIRST>, TaggedHandle<Handle, SECOND>, PortChannelId>;

impl<Handle: ChainHandle, const SIZE: usize> ConnectedChannels<Handle, SIZE> {
    pub fn channel_at<const FIRST: usize, const SECOND: usize>(
        &self,
    ) -> Result<TaggedChannel<Handle, FIRST, SECOND>, Error> {
        let raw_channel = self.raw_channel_at(FIRST, SECOND)?.clone();

        let channel = raw_channel.map_chain(MonoTagged::new, MonoTagged::new);

        Ok(channel)
    }

    pub fn port_channel_id_at<const FIRST: usize, const SECOND: usize>(
        &self,
    ) -> Result<TaggedPortChannelId<Handle, FIRST, SECOND>, Error> {
        let raw_port_channel_id = self.raw_port_channel_id_at(FIRST, SECOND)?.clone();

        Ok(DualTagged::new(raw_port_channel_id))
    }

    pub fn raw_channel_at(
        &self,
        first: usize,
        second: usize,
    ) -> Result<&Channel<Handle, Handle>, Error> {
        if first >= SIZE {
            Err(eyre!("cannot get channel beyond position {}", first))
        } else if second >= SIZE {
            Err(eyre!("cannot get channel beyond position {}", second))
        } else {
            self.channels
                .get(first)
                .and_then(|slice| slice.get(second))
                .ok_or_else(|| {
                    eyre!(
                        "failed to get foreign client at position {}, {}",
                        first,
                        second
                    )
                })
        }
    }

    pub fn raw_port_channel_id_at(
        &self,
        first: usize,
        second: usize,
    ) -> Result<&PortChannelId, Error> {
        if first >= SIZE {
            Err(eyre!(
                "cannot get port channel id beyond position {}",
                first
            ))
        } else if second >= SIZE {
            Err(eyre!(
                "cannot get port channel id beyond position {}",
                second
            ))
        } else {
            self.port_channel_ids
                .get(first)
                .and_then(|slice| slice.get(second))
                .ok_or_else(|| {
                    eyre!(
                        "failed to get foreign client at position {}, {}",
                        first,
                        second
                    )
                })
        }
    }
}

impl<Handle: ChainHandle, const SIZE: usize> TryFrom<DynamicConnectedChannels<Handle>>
    for ConnectedChannels<Handle, SIZE>
{
    type Error = Error;

    fn try_from(channels: DynamicConnectedChannels<Handle>) -> Result<Self, Error> {
        Ok(ConnectedChannels {
            connections: try_into_nested_array(channels.connections)?,
            channels: try_into_nested_array(channels.channels)?,
            port_channel_ids: try_into_nested_array(channels.port_channel_ids)?,
        })
    }
}

impl<Handle: ChainHandle> From<ConnectedChannels<Handle, 2>>
    for BinaryConnectedChannel<Handle, Handle>
{
    fn from(channels: ConnectedChannels<Handle, 2>) -> Self {
        let [[_, connection], _] = channels.connections;
        let [[_, channel], _] = channels.channels;
        let [[_, port_channel_id_a], [port_channel_id_b, _]] = channels.port_channel_ids;

        let connection = ConnectedConnection {
            client: ConnectedClients {
                client_id_a: DualTagged::new(channel.a_side.client_id().clone()),
                client_id_b: DualTagged::new(channel.b_side.client_id().clone()),
            },

            connection,

            connection_id_a: DualTagged::new(channel.a_side.connection_id().clone()),
            connection_id_b: DualTagged::new(channel.b_side.connection_id().clone()),
        };

        Self {
            connection,
            channel,
            channel_id_a: DualTagged::new(port_channel_id_a.channel_id),
            channel_id_b: DualTagged::new(port_channel_id_b.channel_id),
            port_a: DualTagged::new(port_channel_id_a.port_id),
            port_b: DualTagged::new(port_channel_id_b.port_id),
        }
    }
}
