/*!
   Constructs for N-ary connected channels.
*/

use std::collections::HashMap;

use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};

use super::aliases::NthChainHandle;
use crate::error::Error;
use crate::types::binary::channel::ConnectedChannel;
use crate::types::env::{EnvWriter, ExportEnv};
use crate::types::tagged::*;

/**
   A fixed-size N-ary connected channels as specified by `SIZE`.

   Contains `SIZE`x`SIZE` number of binary [`ConnectedChannel`]s.
*/
#[derive(Debug, Clone)]
pub struct ConnectedChannels<Handle: ChainHandle, const SIZE: usize> {
    pub channels: HashMap<usize, HashMap<usize, ConnectedChannel<Handle, Handle>>>,
}

/**
   A dynamic-sized N-ary connected channels, consist of a nested
   vector of binary [`ConnectedChannel`]s which must be of the
   same length.
*/
#[derive(Debug, Clone)]
pub struct DynamicConnectedChannels<Handle: ChainHandle> {
    channels: HashMap<usize, HashMap<usize, ConnectedChannel<Handle, Handle>>>,
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
        let inner_channels = self.channels.get(&CHAIN_A).ok_or_else(|| {
            Error::generic(eyre!("No channel entries found for chain `{CHAIN_A}`"))
        })?;
        let raw_channel = inner_channels
            .get(&CHAIN_B)
            .ok_or_else(|| {
                Error::generic(eyre!(
                    "No channel entry found for chain `{CHAIN_A}` to `{CHAIN_B}`"
                ))
            })?
            .clone();
        let channel = raw_channel.map_chain(MonoTagged::new, MonoTagged::new);

        Ok(channel)
    }

    pub fn channels(&self) -> &HashMap<usize, HashMap<usize, ConnectedChannel<Handle, Handle>>> {
        &self.channels
    }
}

impl<Handle: ChainHandle> DynamicConnectedChannels<Handle> {
    pub fn new(channels: HashMap<usize, HashMap<usize, ConnectedChannel<Handle, Handle>>>) -> Self {
        Self { channels }
    }

    pub fn channels(&self) -> &HashMap<usize, HashMap<usize, ConnectedChannel<Handle, Handle>>> {
        &self.channels
    }
}

impl<Handle: ChainHandle, const SIZE: usize> TryFrom<DynamicConnectedChannels<Handle>>
    for ConnectedChannels<Handle, SIZE>
{
    type Error = Error;

    fn try_from(channels: DynamicConnectedChannels<Handle>) -> Result<Self, Error> {
        Ok(ConnectedChannels {
            channels: channels.channels,
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
        for inner_channels in self.channels.iter() {
            for channel in inner_channels.1.iter() {
                writer.write_env(
                    &format!("CONNECTION_ID_{}_to_{}", inner_channels.0, channel.0),
                    &format!("{}", channel.1.connection.connection_id_a),
                );

                writer.write_env(
                    &format!("CHANNEL_ID_{}_to_{}", inner_channels.0, channel.0),
                    &format!("{}", channel.1.channel_id_a),
                );

                writer.write_env(
                    &format!("PORT_{}_to_{}", inner_channels.0, channel.0),
                    &format!("{}", channel.1.port_a),
                );
            }
        }
    }
}
