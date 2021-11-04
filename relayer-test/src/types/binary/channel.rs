use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel as BaseChannel;

use crate::types::id::*;

#[derive(Debug)]
pub struct Channel<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub channel: BaseChannel<ChainA, ChainB>,
    pub channel_id_a: ChannelId<ChainA, ChainB>,
    pub channel_id_b: ChannelId<ChainB, ChainA>,
    pub port_a: PortId<ChainA, ChainB>,
    pub port_b: PortId<ChainB, ChainA>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> Channel<ChainA, ChainB> {
    pub fn flip(self) -> Channel<ChainB, ChainA> {
        Channel {
            channel: self.channel.flipped(),
            channel_id_a: self.channel_id_b,
            channel_id_b: self.channel_id_a,
            port_a: self.port_b,
            port_b: self.port_a,
        }
    }
}
