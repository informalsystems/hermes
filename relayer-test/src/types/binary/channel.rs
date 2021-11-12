/*!
   Type definitions for channel connected between two chains.
*/

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel;

use crate::types::env::{EnvWriter, ExportEnv};
use crate::types::id::{ChannelId, PortId};

/**
   A channel that is connected between two chains with the full handshake
   completed.

   This is a wrapper around [`Channel`] with infallible retrieval
   of the channel IDs, as the channel handshake has been completed.

   TODO: Also embed connected connection and client information here.
*/
#[derive(Debug)]
pub struct ConnectedChannel<ChainA: ChainHandle, ChainB: ChainHandle> {
    /**
       The underlying relayer [`Channel`].
    */
    pub channel: Channel<ChainA, ChainB>,

    /**
       The channel ID on chain A, corresponding to the channel connected
       to chain B.
    */
    pub channel_id_a: ChannelId<ChainA, ChainB>,

    /**
       The channel ID on chain B, corresponding to the channel connected
       to chain A.
    */
    pub channel_id_b: ChannelId<ChainB, ChainA>,

    /**
       The port ID on chain A, corresponding to the channel connected
       to chain B.
    */
    pub port_a: PortId<ChainA, ChainB>,

    /**
       The port ID on chain B, corresponding to the channel connected
       to chain A.
    */
    pub port_b: PortId<ChainB, ChainA>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ConnectedChannel<ChainA, ChainB> {
    /**
       Flip the position between chain A and chain B.

       The original chain A become the new chain B, and the original chain B
       become the new chain A.
    */
    pub fn flip(self) -> ConnectedChannel<ChainB, ChainA> {
        ConnectedChannel {
            channel: self.channel.flipped(),
            channel_id_a: self.channel_id_b,
            channel_id_b: self.channel_id_a,
            port_a: self.port_b,
            port_b: self.port_a,
        }
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ExportEnv for ConnectedChannel<ChainA, ChainB> {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        writer.write_env("CHANNEL_ID_A", &format!("{}", self.channel_id_a));
        writer.write_env("PORT_A", &format!("{}", self.port_a));
        writer.write_env("CHANNEL_ID_B", &format!("{}", self.channel_id_b));
        writer.write_env("PORT_B", &format!("{}", self.port_b));
    }
}
