/*!
   Constructs for N-ary connected channels.
*/

use core::convert::TryFrom;
use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};

use super::aliases::NthChainHandle;
use crate::error::Error;
use crate::types::binary::channel::ConnectedChannel;
use crate::types::env::{EnvWriter, ExportEnv};
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
   at position `CHAIN_A` and `CHAIN_B`.
*/
pub type NthConnectedChannel<const CHAIN_A: usize, const CHAIN_B: usize, Handle> =
    ConnectedChannel<NthChainHandle<CHAIN_A, Handle>, NthChainHandle<CHAIN_B, Handle>>;

/**
   A tagged [`Channel`] with the A side at `CHAIN_A` position and B side at
   the `CHAIN_B` position.
*/
pub type NthChannel<const CHAIN_A: usize, const CHAIN_B: usize, Handle> =
    Channel<NthChainHandle<CHAIN_A, Handle>, NthChainHandle<CHAIN_B, Handle>>;

/**
   A tagged [`ChannelId`] for the chain at position `CHAIN_A` that is correspond
   to the counterparty chain at position `CHAIN_B`
*/
pub type NthChannelId<const CHAIN_A: usize, const CHAIN_B: usize, Handle> =
    DualTagged<NthChainHandle<CHAIN_A, Handle>, NthChainHandle<CHAIN_B, Handle>, ChannelId>;

/**
   A tagged [`PortId`] for the chain at position `CHAIN_A` that is correspond
   to the counterparty chain at position `CHAIN_B`
*/
pub type NthPortId<const CHAIN_A: usize, const CHAIN_B: usize, Handle> =
    DualTagged<NthChainHandle<CHAIN_A, Handle>, NthChainHandle<CHAIN_B, Handle>, PortId>;

impl<Handle: ChainHandle, const SIZE: usize> ConnectedChannels<Handle, SIZE> {
    /**
       Get the binary [`ConnectedChannel`] at position `CHAIN_A` and `CHAIN_B`,
       which must be less than `SIZE`.
    */
    pub fn channel_at<const CHAIN_A: usize, const CHAIN_B: usize>(
        &self,
    ) -> Result<NthConnectedChannel<CHAIN_A, CHAIN_B, Handle>, Error> {
        if CHAIN_A >= SIZE || CHAIN_B >= SIZE {
            Err(Error::generic(eyre!(
                "cannot get channel beyond position {}/{}",
                CHAIN_A,
                CHAIN_B
            )))
        } else {
            let raw_channel = self.channels[CHAIN_A][CHAIN_B].clone();

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

impl<Handle: ChainHandle> From<ConnectedChannels<Handle, 2>> for NthConnectedChannel<0, 1, Handle> {
    fn from(channels: ConnectedChannels<Handle, 2>) -> Self {
        channels.channel_at::<0, 1>().unwrap()
    }
}

impl<Handle: ChainHandle, const SIZE: usize> ExportEnv for ConnectedChannels<Handle, SIZE> {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        for (i, inner_channels) in self.channels.iter().enumerate() {
            for (j, channel_i_to_j) in inner_channels.iter().enumerate() {
                writer.write_env(
                    &format!("CONNECTION_ID_{j}_to_{i}"),
                    &format!("{}", channel_i_to_j.connection.connection_id_a),
                );

                writer.write_env(
                    &format!("CONNECTION_ID_{i}_to_{j}"),
                    &format!("{}", channel_i_to_j.connection.connection_id_b),
                );

                writer.write_env(
                    &format!("CHANNEL_ID_{j}_to_{i}"),
                    &format!("{}", channel_i_to_j.channel_id_a),
                );

                writer.write_env(
                    &format!("PORT_{j}_to_{i}"),
                    &format!("{}", channel_i_to_j.port_a),
                );

                writer.write_env(
                    &format!("CHANNEL_ID_{i}_to_{j}"),
                    &format!("{}", channel_i_to_j.channel_id_b),
                );

                writer.write_env(
                    &format!("PORT_{i}_to_{j}"),
                    &format!("{}", channel_i_to_j.port_b),
                );
            }
        }
    }
}
