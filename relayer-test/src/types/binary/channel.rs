use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::Channel as BaseChannel;

use crate::tagged::dual::Tagged;

#[derive(Debug)]
pub struct Channel<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub channel: BaseChannel<ChainA, ChainB>,
    pub channel_id_a: Tagged<ChainA, ChainB, ChannelId>,
    pub channel_id_b: Tagged<ChainB, ChainA, ChannelId>,
    pub port_a: Tagged<ChainA, ChainB, PortId>,
    pub port_b: Tagged<ChainB, ChainA, PortId>,
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
