use core::time::Duration;
use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{IncludeProof, QueryChannelRequest, QueryHeight};
use ibc_relayer::channel::{extract_channel_id, Channel, ChannelSide};
use ibc_relayer_types::core::ics04_channel::channel::State as ChannelState;
use ibc_relayer_types::core::ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd, Order};

use crate::error::Error;
use crate::types::id::{
    TaggedChannelId, TaggedChannelIdRef, TaggedClientIdRef, TaggedConnectionIdRef, TaggedPortId,
    TaggedPortIdRef,
};
use crate::types::tagged::DualTagged;
use crate::util::retry::assert_eventually_succeed;

pub trait TaggedChannelEndExt<ChainA, ChainB> {
    fn tagged_counterparty_channel_id(&self) -> Option<TaggedChannelId<ChainB, ChainA>>;
    fn tagged_counterparty_port_id(&self) -> TaggedPortId<ChainB, ChainA>;
}

impl<ChainA, ChainB> TaggedChannelEndExt<ChainA, ChainB>
    for DualTagged<ChainA, ChainB, ChannelEnd>
{
    fn tagged_counterparty_channel_id(&self) -> Option<TaggedChannelId<ChainB, ChainA>> {
        self.contra_map(|c| c.counterparty().channel_id.clone())
            .transpose()
    }

    fn tagged_counterparty_port_id(&self) -> TaggedPortId<ChainB, ChainA> {
        self.contra_map(|c| c.counterparty().port_id.clone())
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
) -> Result<(TaggedChannelId<ChainB, ChainA>, Channel<ChainB, ChainA>), Error> {
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
    let channel_id = extract_channel_id(&event)?.clone();
    let channel2 = Channel::restore_from_event(handle_b.clone(), handle_a.clone(), event)?;

    Ok((DualTagged::new(channel_id), channel2))
}

pub fn try_channel<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: &ChainA,
    handle_b: &ChainB,
    channel: &Channel<ChainB, ChainA>,
) -> Result<(TaggedChannelId<ChainA, ChainB>, Channel<ChainA, ChainB>), Error> {
    let event = channel.build_chan_open_try_and_send()?;
    let channel_id = extract_channel_id(&event)?.clone();
    let channel2 = Channel::restore_from_event(handle_a.clone(), handle_b.clone(), event)?;

    Ok((DualTagged::new(channel_id), channel2))
}

pub fn ack_channel<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: &ChainA,
    handle_b: &ChainB,
    channel: &Channel<ChainB, ChainA>,
) -> Result<(TaggedChannelId<ChainA, ChainB>, Channel<ChainA, ChainB>), Error> {
    let event = channel.build_chan_open_ack_and_send()?;
    let channel_id = extract_channel_id(&event)?.clone();
    let channel2 = Channel::restore_from_event(handle_a.clone(), handle_b.clone(), event)?;

    Ok((DualTagged::new(channel_id), channel2))
}

pub fn query_channel_end<ChainA: ChainHandle, ChainB>(
    handle: &ChainA,
    channel_id: &TaggedChannelIdRef<ChainA, ChainB>,
    port_id: &TaggedPortIdRef<ChainA, ChainB>,
) -> Result<DualTagged<ChainA, ChainB, ChannelEnd>, Error> {
    let (channel_end, _) = handle.query_channel(
        QueryChannelRequest {
            port_id: port_id.into_value().clone(),
            channel_id: channel_id.into_value().clone(),
            height: QueryHeight::Latest,
        },
        IncludeProof::No,
    )?;

    Ok(DualTagged::new(channel_end))
}

pub fn query_identified_channel_end<ChainA: ChainHandle, ChainB>(
    handle: &ChainA,
    channel_id: TaggedChannelIdRef<ChainA, ChainB>,
    port_id: TaggedPortIdRef<ChainA, ChainB>,
) -> Result<DualTagged<ChainA, ChainB, IdentifiedChannelEnd>, Error> {
    let (channel_end, _) = handle.query_channel(
        QueryChannelRequest {
            port_id: port_id.into_value().clone(),
            channel_id: channel_id.into_value().clone(),
            height: QueryHeight::Latest,
        },
        IncludeProof::No,
    )?;
    Ok(DualTagged::new(IdentifiedChannelEnd::new(
        port_id.into_value().clone(),
        channel_id.into_value().clone(),
        channel_end,
    )))
}

pub fn assert_eventually_channel_established<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: &ChainA,
    handle_b: &ChainB,
    channel_id_a: &TaggedChannelIdRef<ChainA, ChainB>,
    port_id_a: &TaggedPortIdRef<ChainA, ChainB>,
) -> Result<TaggedChannelId<ChainB, ChainA>, Error> {
    assert_eventually_succeed(
        "channel should eventually established",
        20,
        Duration::from_secs(1),
        || {
            let channel_end_a = query_channel_end(handle_a, channel_id_a, port_id_a)?;

            if !channel_end_a.value().state_matches(&ChannelState::Open) {
                return Err(Error::generic(eyre!(
                    "expected channel end A to be in open state"
                )));
            }

            let channel_id_b = channel_end_a
                .tagged_counterparty_channel_id()
                .ok_or_else(|| {
                    eyre!("expected counterparty channel id to present on open channel")
                })?;

            let port_id_b = channel_end_a.tagged_counterparty_port_id();

            let channel_end_b =
                query_channel_end(handle_b, &channel_id_b.as_ref(), &port_id_b.as_ref())?;

            if !channel_end_b.value().state_matches(&ChannelState::Open) {
                return Err(Error::generic(eyre!(
                    "expected channel end B to be in open state"
                )));
            }

            Ok(channel_id_b)
        },
    )
}
