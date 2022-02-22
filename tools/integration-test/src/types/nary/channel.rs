/*!
   Constructs for N-ary connected channels.
*/

use core::convert::TryFrom;
use eyre::eyre;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel;

use super::aliases::NthHandle;
use crate::error::Error;
use crate::types::binary::channel::ConnectedChannel;
use crate::types::tagged::*;
use crate::util::array::try_into_nested_array;

/**
   A fixed-size N-ary connected channels as specified by `SIZE`.

   Contains `SIZE`x`SIZE` number of binary [`ConnectedChannel`]s.
*/
#[derive(Debug, Clone)]
pub struct ConnectedChannels<Handle: ChainHandle, const SIZE: usize> {
    channels: [[ConnectedChannel<Handle, Handle>; SIZE]; SIZE],
}

/**
   A dynamic-sized N-ary connected channels, consist of a nested
   vector of binary [`ConnectedChannel`]s which must be of the
   same length.
*/
#[derive(Debug, Clone)]
pub struct DynamicConnectedChannels<Handle: ChainHandle> {
    channels: Vec<Vec<ConnectedChannel<Handle, Handle>>>,
}

/**
   A tagged [`ConnectedChannel`] that is connected between the chains
   at position `FIRST` and `SECOND`.
*/
pub type TaggedConnectedChannel<Handle, const FIRST: usize, const SECOND: usize> =
    ConnectedChannel<NthHandle<Handle, FIRST>, NthHandle<Handle, SECOND>>;

/**
   A tagged [`Channel`] with the A side at `FIRST` position and B side at
   the `SECOND` position.
*/
pub type TaggedChannel<Handle, const FIRST: usize, const SECOND: usize> =
    Channel<NthHandle<Handle, FIRST>, NthHandle<Handle, SECOND>>;

/**
   A tagged [`ChannelId`] for the chain at position `FIRST` that is correspond
   to the counterparty chain at position `SECOND`
*/
pub type TaggedChannelId<Handle, const FIRST: usize, const SECOND: usize> =
    DualTagged<NthHandle<Handle, FIRST>, NthHandle<Handle, SECOND>, ChannelId>;

/**
   A tagged [`PortId`] for the chain at position `FIRST` that is correspond
   to the counterparty chain at position `SECOND`
*/
pub type TaggedPortId<Handle, const FIRST: usize, const SECOND: usize> =
    DualTagged<NthHandle<Handle, FIRST>, NthHandle<Handle, SECOND>, PortId>;

impl<Handle: ChainHandle, const SIZE: usize> ConnectedChannels<Handle, SIZE> {
    /**
       Get the binary [`ConnectedChannel`] at position `FIRST` and `SECOND`,
       which must be less than `SIZE`.
    */
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

    pub fn channels(&self) -> &[[ConnectedChannel<Handle, Handle>; SIZE]; SIZE] {
        &self.channels
    }
}

impl<Handle: ChainHandle> DynamicConnectedChannels<Handle> {
    pub fn new(channels: Vec<Vec<ConnectedChannel<Handle, Handle>>>) -> Self {
        Self { channels }
    }

    pub fn channels(&self) -> &Vec<Vec<ConnectedChannel<Handle, Handle>>> {
        &self.channels
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
