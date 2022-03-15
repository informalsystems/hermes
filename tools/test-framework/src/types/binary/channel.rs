/*!
   Type definitions for channel connected between two chains.
*/

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel;

use super::connection::ConnectedConnection;
use crate::types::env::{EnvWriter, ExportEnv};
use crate::types::id::{TaggedChannelId, TaggedPortId};

/**
   A channel that is connected between two chains with the full handshake
   completed.

   This is a wrapper around [`Channel`] with infallible retrieval
   of the channel IDs, as the channel handshake has been completed.
*/
#[derive(Debug, Clone)]
pub struct ConnectedChannel<ChainA: ChainHandle, ChainB: ChainHandle> {
    /**
      The underlying [`ConnectedConnection`] that the channel operates on.
    */
    pub connection: ConnectedConnection<ChainA, ChainB>,

    /**
       The underlying relayer [`Channel`].
    */
    pub channel: Channel<ChainA, ChainB>,

    /**
       The channel ID on chain A, corresponding to the channel connected
       to chain B.
    */
    pub channel_id_a: TaggedChannelId<ChainA, ChainB>,

    /**
       The channel ID on chain B, corresponding to the channel connected
       to chain A.
    */
    pub channel_id_b: TaggedChannelId<ChainB, ChainA>,

    /**
       The port ID on chain A, corresponding to the channel connected
       to chain B.
    */
    pub port_a: TaggedPortId<ChainA, ChainB>,

    /**
       The port ID on chain B, corresponding to the channel connected
       to chain A.
    */
    pub port_b: TaggedPortId<ChainB, ChainA>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ConnectedChannel<ChainA, ChainB> {
    /**
       Flip the position between chain A and chain B.

       The original chain A become the new chain B, and the original chain B
       become the new chain A.
    */
    pub fn flip(self) -> ConnectedChannel<ChainB, ChainA> {
        ConnectedChannel {
            connection: self.connection.flip(),
            channel: self.channel.flipped(),
            channel_id_a: self.channel_id_b,
            channel_id_b: self.channel_id_a,
            port_a: self.port_b,
            port_b: self.port_a,
        }
    }

    pub fn map_chain<ChainC: ChainHandle, ChainD: ChainHandle>(
        self,
        map_a: impl Fn(ChainA) -> ChainC,
        map_b: impl Fn(ChainB) -> ChainD,
    ) -> ConnectedChannel<ChainC, ChainD> {
        ConnectedChannel {
            connection: self.connection.map_chain(&map_a, &map_b),
            channel: self.channel.map_chain(&map_a, &map_b),
            channel_id_a: self.channel_id_a.retag(),
            channel_id_b: self.channel_id_b.retag(),
            port_a: self.port_a.retag(),
            port_b: self.port_b.retag(),
        }
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ExportEnv for ConnectedChannel<ChainA, ChainB> {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        self.connection.export_env(writer);
        writer.write_env("CHANNEL_ID_A", &format!("{}", self.channel_id_a));
        writer.write_env("PORT_A", &format!("{}", self.port_a));
        writer.write_env("CHANNEL_ID_B", &format!("{}", self.channel_id_b));
        writer.write_env("PORT_B", &format!("{}", self.port_b));
    }
}
