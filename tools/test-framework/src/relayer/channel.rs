use core::time::Duration;
use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{IncludeProof, QueryChannelRequest, QueryHeight};
use ibc_relayer::channel::{extract_channel_id, Channel, ChannelSide};
use ibc_relayer_types::core::ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd, Order};
use ibc_relayer_types::core::ics04_channel::channel::{Ordering, State as ChannelState};
use ibc_relayer_types::core::ics04_channel::timeout::UpgradeTimeout;
use ibc_relayer_types::core::ics04_channel::version::Version;
use ibc_relayer_types::core::ics24_host::identifier::ConnectionId;

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

pub struct ChannelUpgradeAssertionAttributes {
    old_version: Version,
    old_ordering: Ordering,
    old_connection_hops_a: Vec<ConnectionId>,
    old_connection_hops_b: Vec<ConnectionId>,
    new_version: Version,
    new_ordering: Ordering,
    new_connection_hops_a: Vec<ConnectionId>,
    new_connection_hops_b: Vec<ConnectionId>,
}

impl ChannelUpgradeAssertionAttributes {
    pub fn new(
        old_version: Version,
        old_ordering: Ordering,
        old_connection_hops_a: Vec<ConnectionId>,
        old_connection_hops_b: Vec<ConnectionId>,
        new_version: Version,
        new_ordering: Ordering,
        new_connection_hops_a: Vec<ConnectionId>,
        new_connection_hops_b: Vec<ConnectionId>,
    ) -> Self {
        Self {
            old_version,
            old_ordering,
            old_connection_hops_a,
            old_connection_hops_b,
            new_version,
            new_ordering,
            new_connection_hops_a,
            new_connection_hops_b,
        }
    }

    pub fn old_version(&self) -> &Version {
        &self.old_version
    }

    pub fn old_ordering(&self) -> &Ordering {
        &self.old_ordering
    }

    pub fn old_connection_hops_a(&self) -> &Vec<ConnectionId> {
        &self.old_connection_hops_a
    }

    pub fn old_connection_hops_b(&self) -> &Vec<ConnectionId> {
        &self.old_connection_hops_b
    }

    pub fn new_version(&self) -> &Version {
        &self.new_version
    }

    pub fn new_ordering(&self) -> &Ordering {
        &self.new_ordering
    }

    pub fn new_connection_hops_a(&self) -> &Vec<ConnectionId> {
        &self.new_connection_hops_a
    }

    pub fn new_connection_hops_b(&self) -> &Vec<ConnectionId> {
        &self.new_connection_hops_b
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

pub fn init_channel_optimistic<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: &ChainA,
    handle_b: &ChainB,
    client_id_a: &TaggedClientIdRef<ChainA, ChainB>,
    client_id_b: &TaggedClientIdRef<ChainB, ChainA>,
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
            ConnectionId::default(),
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
    Ok(DualTagged::new(channel_id))
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

pub fn init_channel_upgrade<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: &ChainA,
    handle_b: &ChainB,
    channel: Channel<ChainA, ChainB>,
    new_version: Option<Version>,
    new_ordering: Option<Order>,
    new_connection_hops: Option<Vec<ConnectionId>>,
    timeout: UpgradeTimeout,
) -> Result<(TaggedChannelId<ChainB, ChainA>, Channel<ChainB, ChainA>), Error> {
    let event = channel.build_chan_upgrade_init_and_send(
        new_version,
        new_ordering,
        new_connection_hops,
        timeout,
    )?;
    let channel_id = extract_channel_id(&event)?.clone();
    let channel2 = Channel::restore_from_event(handle_b.clone(), handle_a.clone(), event)?;
    Ok((DualTagged::new(channel_id), channel2))
}

pub fn assert_eventually_channel_upgrade_init<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: &ChainA,
    handle_b: &ChainB,
    channel_id_a: &TaggedChannelIdRef<ChainA, ChainB>,
    port_id_a: &TaggedPortIdRef<ChainA, ChainB>,
    upgrade_attrs: &ChannelUpgradeAssertionAttributes,
) -> Result<TaggedChannelId<ChainB, ChainA>, Error> {
    assert_eventually_succeed(
        "channel upgrade should be initialised",
        20,
        Duration::from_secs(1),
        || {
            assert_eventually_succeed(
                "channel upgrade should be initialised",
                20,
                Duration::from_secs(1),
                || {
                    assert_channel_upgrade_state(
                        ChannelState::InitUpgrade,
                        ChannelState::Open,
                        handle_a,
                        handle_b,
                        channel_id_a,
                        port_id_a,
                        upgrade_attrs,
                    )
                },
            )
        },
    )
}

pub fn try_channel_upgrade<ChainA: ChainHandle, ChainB: ChainHandle>(
    _handle_a: &ChainA,
    _handle_b: &ChainB,
    _channel: Channel<ChainA, ChainB>,
) { // -> Result<(TaggedChannelId<ChainB, ChainA>, Channel<ChainB, ChainA>), Error> {
     //let event = channel.build_chan_upgrade_try_and_send()?;
     //let channel_id = extract_channel_id(&event)?.clone();
     //let channel2 = Channel::restore_from_event(handle_b.clone(), handle_a.clone(), event)?;
     //Ok((DualTagged::new(channel_id), channel2))
}

pub fn assert_eventually_channel_upgrade_try<ChainA: ChainHandle, ChainB: ChainHandle>(
    handle_a: &ChainA,
    handle_b: &ChainB,
    channel_id_a: &TaggedChannelIdRef<ChainA, ChainB>,
    port_id_a: &TaggedPortIdRef<ChainA, ChainB>,
    upgrade_attrs: &ChannelUpgradeAssertionAttributes,
) -> Result<TaggedChannelId<ChainB, ChainA>, Error> {
    assert_eventually_succeed(
        "channel upgrade should be initialised",
        20,
        Duration::from_secs(1),
        || {
            assert_channel_upgrade_state(
                ChannelState::InitUpgrade,
                ChannelState::TryUpgrade,
                handle_a,
                handle_b,
                channel_id_a,
                port_id_a,
                upgrade_attrs,
            )
        },
    )
}

fn assert_channel_upgrade_state<ChainA: ChainHandle, ChainB: ChainHandle>(
    a_side_state: ChannelState,
    b_side_state: ChannelState,
    handle_a: &ChainA,
    handle_b: &ChainB,
    channel_id_a: &TaggedChannelIdRef<ChainA, ChainB>,
    port_id_a: &TaggedPortIdRef<ChainA, ChainB>,
    upgrade_attrs: &ChannelUpgradeAssertionAttributes,
) -> Result<TaggedChannelId<ChainB, ChainA>, Error> {
    let channel_end_a = query_channel_end(handle_a, channel_id_a, port_id_a)?;

    if !channel_end_a.value().state_matches(&a_side_state) {
        return Err(Error::generic(eyre!(
            "expected channel end A to `{}`, but is instead `{}`",
            a_side_state,
            channel_end_a.value().state()
        )));
    }

    if !channel_end_a
        .value()
        .version_matches(upgrade_attrs.new_version())
    {
        return Err(Error::generic(eyre!(
            "expected channel end A version to be `{}`, but it is instead `{}`",
            upgrade_attrs.new_version(),
            channel_end_a.value().version()
        )));
    }

    if !channel_end_a
        .value()
        .order_matches(upgrade_attrs.new_ordering())
    {
        return Err(Error::generic(eyre!(
            "expected channel end A ordering to be `{}`, but it is instead `{}`",
            upgrade_attrs.new_ordering(),
            channel_end_a.value().ordering()
        )));
    }

    if !channel_end_a
        .value()
        .connection_hops_matches(upgrade_attrs.new_connection_hops_a())
    {
        return Err(Error::generic(eyre!(
            "expected channel end A connection hops to be `{:?}`, but it is instead `{:?}`",
            upgrade_attrs.new_connection_hops_a(),
            channel_end_a.value().connection_hops()
        )));
    }

    let channel_id_b = channel_end_a
        .tagged_counterparty_channel_id()
        .ok_or_else(|| eyre!("expected counterparty channel id to present on open channel"))?;

    let port_id_b = channel_end_a.tagged_counterparty_port_id();

    let channel_end_b = query_channel_end(handle_b, &channel_id_b.as_ref(), &port_id_b.as_ref())?;

    if !channel_end_b.value().state_matches(&b_side_state) {
        return Err(Error::generic(eyre!(
            "expected channel end B to be in open state"
        )));
    }

    if !channel_end_b
        .value()
        .version_matches(upgrade_attrs.old_version())
    {
        return Err(Error::generic(eyre!(
            "expected channel end B version to be `{}`, but it is instead `{}`",
            upgrade_attrs.new_version(),
            channel_end_b.value().version()
        )));
    }

    if !channel_end_b
        .value()
        .order_matches(upgrade_attrs.old_ordering())
    {
        return Err(Error::generic(eyre!(
            "expected channel end B ordering to be `{}`, but it is instead `{}`",
            upgrade_attrs.new_ordering(),
            channel_end_b.value().ordering()
        )));
    }

    if !channel_end_b
        .value()
        .connection_hops_matches(upgrade_attrs.old_connection_hops_b())
    {
        return Err(Error::generic(eyre!(
            "expected channel end B connection hops to be `{:?}`, but it is instead `{:?}`",
            upgrade_attrs.new_connection_hops_b(),
            channel_end_b.value().connection_hops()
        )));
    }

    Ok(channel_id_b)
}
