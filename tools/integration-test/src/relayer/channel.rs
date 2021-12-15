use ibc::core::ics04_channel::channel::{ChannelEnd, Order};
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::channel::{extract_channel_id, Channel, ChannelSide};

use crate::error::Error;
use crate::types::id::{
    TaggedChannelId, TaggedChannelIdRef, TaggedClientIdRef, TaggedConnectionIdRef, TaggedPortIdRef,
};
use crate::types::tagged::DualTagged;

pub trait TaggedChannelEndExt<ChainA, ChainB> {
    fn tagged_counterparty_channel_id(&self) -> Option<TaggedChannelId<ChainB, ChainA>>;
}

impl<ChainA, ChainB> TaggedChannelEndExt<ChainA, ChainB>
    for DualTagged<ChainA, ChainB, ChannelEnd>
{
    fn tagged_counterparty_channel_id(&self) -> Option<TaggedChannelId<ChainB, ChainA>> {
        self.contra_map(|c| c.counterparty().channel_id.clone())
            .transpose()
    }
}

pub fn init_channel<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: &ChainA,
    handle_b: &ChainB,
    client_id_a: &TaggedClientIdRef<ChainA, ChainB>,
    client_id_b: &TaggedClientIdRef<ChainB, ChainA>,
    connection_id_a: &TaggedConnectionIdRef<ChainA, ChainB>,
    connection_id_b: &TaggedConnectionIdRef<ChainB, ChainA>,
    src_port_id: &TaggedPortIdRef<ChainA, ChainB>,
    dst_port_id: &TaggedPortIdRef<ChainB, ChainA>,
) -> Result<TaggedChannelId<ChainB, ChainA>, Error> {
    let channel = Channel {
        connection_delay: Default::default(),
        ordering: Order::Unordered,
        a_side: ChannelSide::new(
            handle_a.clone(),
            client_id_a.cloned_value(),
            connection_id_a.cloned_value(),
            src_port_id.cloned_value(),
            None,
            None,
        ),
        b_side: ChannelSide::new(
            handle_b.clone(),
            client_id_b.cloned_value(),
            connection_id_b.cloned_value(),
            dst_port_id.cloned_value(),
            None,
            None,
        ),
    };

    let event = channel.build_chan_open_init_and_send()?;

    let channel_id = extract_channel_id(&event)?;

    Ok(DualTagged::new(channel_id.clone()))
}

pub fn query_channel_end<ChainA: ChainHandle, ChainB>(
    handle: &ChainA,
    channel_id: &TaggedChannelIdRef<ChainA, ChainB>,
    port_id: &TaggedPortIdRef<ChainA, ChainB>,
) -> Result<DualTagged<ChainA, ChainB, ChannelEnd>, Error> {
    let channel_end = handle.query_channel(port_id.value(), channel_id.value(), Height::zero())?;

    Ok(DualTagged::new(channel_end))
}
