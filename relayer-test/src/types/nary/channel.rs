use eyre::eyre;
use ibc::core::ics24_host::identifier::{ChannelId, PortChannelId, PortId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel;

use super::chains::TaggedHandle;
use crate::error::Error;
use crate::types::tagged::*;

pub type TaggedChannel<Handle, const FIRST: usize, const SECOND: usize> =
    Channel<TaggedHandle<Handle, FIRST>, TaggedHandle<Handle, SECOND>>;

pub type TaggedChannelId<Handle, const FIRST: usize, const SECOND: usize> =
    DualTagged<TaggedHandle<Handle, FIRST>, TaggedHandle<Handle, SECOND>, ChannelId>;

pub type TaggedPortId<Handle, const FIRST: usize, const SECOND: usize> =
    DualTagged<TaggedHandle<Handle, FIRST>, TaggedHandle<Handle, SECOND>, PortId>;

pub type TaggedPortChannelId<Handle, const FIRST: usize, const SECOND: usize> =
    DualTagged<TaggedHandle<Handle, FIRST>, TaggedHandle<Handle, SECOND>, PortChannelId>;

pub struct ConnectedChannels<Handle: ChainHandle, const SIZE: usize> {
    pub channels: [[Channel<Handle, Handle>; SIZE]; SIZE],
    pub port_channel_ids: [[PortChannelId; SIZE]; SIZE],
}

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
