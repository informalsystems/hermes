use core::convert::TryFrom;
use eyre::eyre;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel;

use super::chains::TaggedHandle;
use crate::error::Error;
use crate::types::binary::channel::ConnectedChannel;
use crate::types::tagged::*;
use crate::util::array::try_into_nested_array;

#[derive(Debug, Clone)]
pub struct ConnectedChannels<Handle: ChainHandle, const SIZE: usize> {
    pub channels: [[ConnectedChannel<Handle, Handle>; SIZE]; SIZE],
}

#[derive(Debug, Clone)]
pub struct DynamicConnectedChannels<Handle: ChainHandle> {
    pub channels: Vec<Vec<ConnectedChannel<Handle, Handle>>>,
}

pub type TaggedConnectedChannel<Handle, const FIRST: usize, const SECOND: usize> =
    ConnectedChannel<TaggedHandle<Handle, FIRST>, TaggedHandle<Handle, SECOND>>;

pub type TaggedChannel<Handle, const FIRST: usize, const SECOND: usize> =
    Channel<TaggedHandle<Handle, FIRST>, TaggedHandle<Handle, SECOND>>;

pub type TaggedChannelId<Handle, const FIRST: usize, const SECOND: usize> =
    DualTagged<TaggedHandle<Handle, FIRST>, TaggedHandle<Handle, SECOND>, ChannelId>;

pub type TaggedPortId<Handle, const FIRST: usize, const SECOND: usize> =
    DualTagged<TaggedHandle<Handle, FIRST>, TaggedHandle<Handle, SECOND>, PortId>;

impl<Handle: ChainHandle, const SIZE: usize> ConnectedChannels<Handle, SIZE> {
    pub fn channel_at<const FIRST: usize, const SECOND: usize>(
        &self,
    ) -> Result<TaggedConnectedChannel<Handle, FIRST, SECOND>, Error> {
        if FIRST >= SIZE || SECOND >= SIZE {
            Err(Error::generic(eyre!(
                "cannot get channel beyond position {}/{}",
                FIRST,
                SECOND
            )))
        } else {
            let raw_channel = self.channels[FIRST][SECOND].clone();

            let channel = raw_channel.map_chain(MonoTagged::new, MonoTagged::new);

            Ok(channel)
        }
    }
}

impl<Handle: ChainHandle, const SIZE: usize> TryFrom<DynamicConnectedChannels<Handle>>
    for ConnectedChannels<Handle, SIZE>
{
    type Error = Error;

    fn try_from(channels: DynamicConnectedChannels<Handle>) -> Result<Self, Error> {
        Ok(ConnectedChannels {
            channels: try_into_nested_array(channels.channels)?,
        })
    }
}

impl<Handle: ChainHandle> From<ConnectedChannels<Handle, 2>>
    for TaggedConnectedChannel<Handle, 0, 1>
{
    fn from(channels: ConnectedChannels<Handle, 2>) -> Self {
        channels.channel_at::<0, 1>().unwrap()
    }
}
