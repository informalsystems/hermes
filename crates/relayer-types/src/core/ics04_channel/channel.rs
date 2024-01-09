use crate::utils::pretty::PrettySlice;

use std::fmt::{Display, Error as FmtError, Formatter};
use std::str::FromStr;

use ibc_proto::Protobuf;
use serde::{Deserialize, Serialize};

use ibc_proto::ibc::core::channel::v1::{
    Channel as RawChannel, Counterparty as RawCounterparty,
    IdentifiedChannel as RawIdentifiedChannel,
};

use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics04_channel::{error::Error, version::Version};
use crate::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IdentifiedChannelEnd {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub channel_end: ChannelEnd,
}

impl IdentifiedChannelEnd {
    pub fn new(port_id: PortId, channel_id: ChannelId, channel_end: ChannelEnd) -> Self {
        IdentifiedChannelEnd {
            port_id,
            channel_id,
            channel_end,
        }
    }
}

impl Protobuf<RawIdentifiedChannel> for IdentifiedChannelEnd {}

impl TryFrom<RawIdentifiedChannel> for IdentifiedChannelEnd {
    type Error = Error;

    fn try_from(value: RawIdentifiedChannel) -> Result<Self, Self::Error> {
        let raw_channel_end = RawChannel {
            state: value.state,
            ordering: value.ordering,
            counterparty: value.counterparty,
            connection_hops: value.connection_hops,
            version: value.version,
            upgrade_sequence: 0, // FIXME: proto IdentifiedChannel does not have this field, should we default to 0 ?
        };

        Ok(IdentifiedChannelEnd {
            port_id: value.port_id.parse().map_err(Error::identifier)?,
            channel_id: value.channel_id.parse().map_err(Error::identifier)?,
            channel_end: raw_channel_end.try_into()?,
        })
    }
}

impl From<IdentifiedChannelEnd> for RawIdentifiedChannel {
    fn from(value: IdentifiedChannelEnd) -> Self {
        RawIdentifiedChannel {
            state: value.channel_end.state.as_i32(),
            ordering: value.channel_end.ordering as i32,
            counterparty: Some(value.channel_end.counterparty().clone().into()),
            connection_hops: value
                .channel_end
                .connection_hops
                .iter()
                .map(|v| v.as_str().to_string())
                .collect(),
            version: value.channel_end.version.to_string(),
            port_id: value.port_id.to_string(),
            channel_id: value.channel_id.to_string(),
            upgrade_sequence: value.channel_end.upgraded_sequence.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChannelEnd {
    pub state: State,
    pub ordering: Ordering,
    pub remote: Counterparty,
    pub connection_hops: Vec<ConnectionId>,
    pub version: Version,
    pub upgraded_sequence: Sequence,
}

impl Display for ChannelEnd {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "ChannelEnd {{ state: {}, ordering: {}, remote: {}, connection_hops: {}, version: {} }}",
            self.state, self.ordering, self.remote, PrettySlice(&self.connection_hops), self.version
        )
    }
}

impl Default for ChannelEnd {
    fn default() -> Self {
        ChannelEnd {
            state: State::Uninitialized,
            ordering: Default::default(),
            remote: Counterparty::default(),
            connection_hops: Vec::new(),
            version: Version::default(),
            upgraded_sequence: Sequence::from(0), // The value of 0 indicates the channel has never been upgraded
        }
    }
}

impl Protobuf<RawChannel> for ChannelEnd {}

impl TryFrom<RawChannel> for ChannelEnd {
    type Error = Error;

    fn try_from(value: RawChannel) -> Result<Self, Self::Error> {
        let chan_state: State = State::from_i32(value.state)?;

        if chan_state == State::Uninitialized {
            return Ok(ChannelEnd::default());
        }

        let chan_ordering = Ordering::from_i32(value.ordering)?;

        // Assemble the 'remote' attribute of the Channel, which represents the Counterparty.
        let remote = value
            .counterparty
            .ok_or_else(Error::missing_counterparty)?
            .try_into()?;

        // Parse each item in connection_hops into a ConnectionId.
        let connection_hops = value
            .connection_hops
            .into_iter()
            .map(|conn_id| ConnectionId::from_str(conn_id.as_str()))
            .collect::<Result<Vec<_>, _>>()
            .map_err(Error::identifier)?;

        let version = value.version.into();

        Ok(ChannelEnd::new(
            chan_state,
            chan_ordering,
            remote,
            connection_hops,
            version,
            Sequence::from(value.upgrade_sequence),
        ))
    }
}

impl From<ChannelEnd> for RawChannel {
    fn from(value: ChannelEnd) -> Self {
        RawChannel {
            state: value.state.as_i32(),
            ordering: value.ordering as i32,
            counterparty: Some(value.counterparty().clone().into()),
            connection_hops: value
                .connection_hops
                .iter()
                .map(|v| v.as_str().to_string())
                .collect(),
            version: value.version.to_string(),
            upgrade_sequence: value.upgraded_sequence.into(),
        }
    }
}

impl ChannelEnd {
    /// Creates a new ChannelEnd in state Uninitialized and other fields parametrized.
    pub fn new(
        state: State,
        ordering: Ordering,
        remote: Counterparty,
        connection_hops: Vec<ConnectionId>,
        version: Version,
        upgraded_sequence: Sequence,
    ) -> Self {
        Self {
            state,
            ordering,
            remote,
            connection_hops,
            version,
            upgraded_sequence,
        }
    }

    /// Updates the ChannelEnd to assume a new State 's'.
    pub fn set_state(&mut self, s: State) {
        self.state = s;
    }

    pub fn set_version(&mut self, v: Version) {
        self.version = v;
    }

    pub fn set_counterparty_channel_id(&mut self, c: ChannelId) {
        self.remote.channel_id = Some(c);
    }

    /// Returns `true` if this `ChannelEnd` is in state [`State::Open`]
    /// [`State::Open(UpgradeState::Upgrading)`] is only used in the channel upgrade
    /// handshake so this method matches with [`State::Open(UpgradeState::NotUpgrading)`].
    pub fn is_open(&self) -> bool {
        self.state_matches(&State::Open(UpgradeState::NotUpgrading))
    }

    pub fn state(&self) -> &State {
        &self.state
    }

    pub fn ordering(&self) -> &Ordering {
        &self.ordering
    }

    pub fn counterparty(&self) -> &Counterparty {
        &self.remote
    }

    pub fn connection_hops(&self) -> &Vec<ConnectionId> {
        &self.connection_hops
    }

    pub fn version(&self) -> &Version {
        &self.version
    }

    pub fn validate_basic(&self) -> Result<(), Error> {
        if self.connection_hops.len() != 1 {
            return Err(Error::invalid_connection_hops_length(
                1,
                self.connection_hops.len(),
            ));
        }
        self.counterparty().validate_basic()
    }

    /// Helper function to compare the state of this end with another state.
    pub fn state_matches(&self, other: &State) -> bool {
        self.state() == other
    }

    /// Helper function to compare the order of this end with another order.
    pub fn order_matches(&self, other: &Ordering) -> bool {
        self.ordering() == other
    }

    #[allow(clippy::ptr_arg)]
    pub fn connection_hops_matches(&self, other: &Vec<ConnectionId>) -> bool {
        self.connection_hops() == other
    }

    pub fn counterparty_matches(&self, other: &Counterparty) -> bool {
        self.counterparty() == other
    }

    pub fn version_matches(&self, other: &Version) -> bool {
        self.version() == other
    }

    /// Returns whether or not the channel with this state is
    /// being upgraded.
    pub fn is_upgrading(&self, other: &Option<IdentifiedChannelEnd>) -> bool {
        use State::*;

        match other {
            Some(other) => {
                let check_sequence = self.upgraded_sequence != other.channel_end.upgraded_sequence;

                let check_state = match self.state {
                    Open(UpgradeState::NotUpgrading) => matches!(
                        other.channel_end.state,
                        Open(UpgradeState::Upgrading) | Flushing | Flushcomplete
                    ),
                    Open(UpgradeState::Upgrading) | Flushing | Flushcomplete => true,
                    _ => false,
                };
                check_sequence || check_state
            }
            None => false,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Counterparty {
    pub port_id: PortId,
    pub channel_id: Option<ChannelId>,
}

impl Counterparty {
    pub fn new(port_id: PortId, channel_id: Option<ChannelId>) -> Self {
        Self {
            port_id,
            channel_id,
        }
    }

    pub fn port_id(&self) -> &PortId {
        &self.port_id
    }

    pub fn channel_id(&self) -> Option<&ChannelId> {
        self.channel_id.as_ref()
    }

    pub fn validate_basic(&self) -> Result<(), Error> {
        Ok(())
    }
}

impl Display for Counterparty {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match &self.channel_id {
            Some(channel_id) => write!(
                f,
                "Counterparty(port_id: {}, channel_id: {})",
                self.port_id, channel_id
            ),
            None => write!(
                f,
                "Counterparty(port_id: {}, channel_id: None)",
                self.port_id
            ),
        }
    }
}

impl Protobuf<RawCounterparty> for Counterparty {}

impl TryFrom<RawCounterparty> for Counterparty {
    type Error = Error;

    fn try_from(value: RawCounterparty) -> Result<Self, Self::Error> {
        let channel_id = Some(value.channel_id)
            .filter(|x| !x.is_empty())
            .map(|v| FromStr::from_str(v.as_str()))
            .transpose()
            .map_err(Error::identifier)?;
        Ok(Counterparty::new(
            value.port_id.parse().map_err(Error::identifier)?,
            channel_id,
        ))
    }
}

impl From<Counterparty> for RawCounterparty {
    fn from(value: Counterparty) -> Self {
        RawCounterparty {
            port_id: value.port_id.as_str().to_string(),
            channel_id: value
                .channel_id
                .map_or_else(|| "".to_string(), |v| v.to_string()),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize, Serialize, Default)]
pub enum Ordering {
    Uninitialized = 0,
    #[default]
    Unordered = 1,
    Ordered = 2,
}

impl Display for Ordering {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "{}", self.as_str())
    }
}

impl Ordering {
    /// Yields the Order as a string
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Uninitialized => "UNINITIALIZED",
            Self::Unordered => "ORDER_UNORDERED",
            Self::Ordered => "ORDER_ORDERED",
        }
    }

    // Parses the Order out from a i32.
    pub fn from_i32(nr: i32) -> Result<Self, Error> {
        match nr {
            0 => Ok(Self::Uninitialized),
            1 => Ok(Self::Unordered),
            2 => Ok(Self::Ordered),

            _ => Err(Error::unknown_order_type(nr.to_string())),
        }
    }
}

impl FromStr for Ordering {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().trim_start_matches("order_") {
            "uninitialized" => Ok(Self::Uninitialized),
            "unordered" => Ok(Self::Unordered),
            "ordered" => Ok(Self::Ordered),
            _ => Err(Error::unknown_order_type(s.to_string())),
        }
    }
}

/// This enum is used to differentiate if a channel is being upgraded when
/// a `UpgradeInitChannel` or a `UpgradeOpenChannel` is received.
/// See `handshake_step` method in `crates/relayer/src/channel.rs`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum UpgradeState {
    Upgrading,
    NotUpgrading,
}

/// The possible state variants that a channel can exhibit.
///
/// These are encoded with integer discriminants so that there is
/// an easy way to compare channel states against one another. More
/// explicitly, this is an attempt to capture the lifecycle of a
/// channel, beginning from the `Uninitialized` state, through the
/// `Open` state, before finally being `Closed`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Deserialize)]
pub enum State {
    /// Default state
    Uninitialized,
    /// A channel has just started the opening handshake.
    Init,
    /// A channel has acknowledged the handshake step on the counterparty chain.
    TryOpen,
    /// A channel has completed the handshake step. Open channels are ready to
    /// send and receive packets.
    /// During some steps of channel upgrades, the state is still in Open. The
    /// `UpgradeState` is used to differentiate these states during the upgrade
    /// handshake.
    /// <https://github.com/cosmos/ibc/blob/main/spec/core/ics-004-channel-and-packet-semantics/UPGRADES.md#upgrade-handshake>
    Open(UpgradeState),
    /// A channel has been closed and can no longer be used to send or receive
    /// packets.
    Closed,
    /// A channel has just accepted the upgrade handshake attempt and is flushing in-flight packets.
    Flushing,
    /// A channel has just completed flushing any in-flight packets.
    Flushcomplete,
}

impl Serialize for State {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Self::Uninitialized => serializer.serialize_str("Uninitialized"),
            Self::Init => serializer.serialize_str("Init"),
            Self::TryOpen => serializer.serialize_str("TryOpen"),
            Self::Open(_) => serializer.serialize_str("Open"),
            Self::Closed => serializer.serialize_str("Closed"),
            Self::Flushing => serializer.serialize_str("Flushing"),
            Self::Flushcomplete => serializer.serialize_str("Flushcomplete"),
        }
    }
}

impl State {
    /// Yields the state as a string
    pub fn as_string(&self) -> &'static str {
        match self {
            Self::Uninitialized => "UNINITIALIZED",
            Self::Init => "INIT",
            Self::TryOpen => "TRYOPEN",
            Self::Open(_) => "OPEN",
            Self::Closed => "CLOSED",
            Self::Flushing => "FLUSHING",
            Self::Flushcomplete => "FLUSHCOMPLETE",
        }
    }

    // Parses the State out from a i32.
    pub fn from_i32(s: i32) -> Result<Self, Error> {
        match s {
            0 => Ok(Self::Uninitialized),
            1 => Ok(Self::Init),
            2 => Ok(Self::TryOpen),
            3 => Ok(Self::Open(UpgradeState::NotUpgrading)),
            4 => Ok(Self::Closed),
            5 => Ok(Self::Flushing),
            6 => Ok(Self::Flushcomplete),
            _ => Err(Error::unknown_state(s)),
        }
    }

    // Parses the State out from a i32.
    pub fn as_i32(&self) -> i32 {
        match self {
            State::Uninitialized => 0,
            State::Init => 1,
            State::TryOpen => 2,
            State::Open(_) => 3,
            State::Closed => 4,
            State::Flushing => 5,
            State::Flushcomplete => 6,
        }
    }

    /// Returns whether or not this channel state is `Open`.
    pub fn is_open(self) -> bool {
        self == State::Open(UpgradeState::NotUpgrading)
    }

    /// Returns whether or not this channel state is `Closed`.
    pub fn is_closed(self) -> bool {
        self == State::Closed
    }

    /// Returns whether or not the channel with this state
    /// has progressed less or the same than the argument.
    /// This only takes into account the open channel handshake.
    ///
    /// # Example
    /// ```rust,ignore
    /// assert!(State::Init.less_or_equal_progress(State::Open));
    /// assert!(State::TryOpen.less_or_equal_progress(State::TryOpen));
    /// assert!(!State::Closed.less_or_equal_progress(State::Open));
    /// ```
    pub fn less_or_equal_progress(self, other: Self) -> bool {
        use State::*;

        match self {
            Uninitialized => true,

            Init => !matches!(other, Uninitialized),
            TryOpen => !matches!(other, Uninitialized | Init),
            Open(UpgradeState::NotUpgrading) => !matches!(other, Uninitialized | Init | TryOpen),
            _ => false,
        }
    }
}

/// Provides a `to_string` method.
impl Display for State {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "{}", self.as_string())
    }
}

#[cfg(test)]
pub mod test_util {
    use crate::core::ics24_host::identifier::{ChannelId, ConnectionId, PortId};

    use ibc_proto::ibc::core::channel::v1::Channel as RawChannel;
    use ibc_proto::ibc::core::channel::v1::Counterparty as RawCounterparty;

    /// Returns a dummy `RawCounterparty`, for testing only!
    /// Can be optionally parametrized with a specific channel identifier.
    pub fn get_dummy_raw_counterparty() -> RawCounterparty {
        RawCounterparty {
            port_id: PortId::default().to_string(),
            channel_id: ChannelId::default().to_string(),
        }
    }

    /// Returns a dummy `RawChannel`, for testing only!
    pub fn get_dummy_raw_channel_end() -> RawChannel {
        RawChannel {
            state: 1,
            ordering: 2,
            counterparty: Some(get_dummy_raw_counterparty()),
            connection_hops: vec![ConnectionId::default().to_string()],
            version: "ics20".to_string(), // The version is not validated.
            upgrade_sequence: 0, // The value of 0 indicates the channel has never been upgraded
        }
    }
}

#[cfg(test)]
mod tests {

    use core::str::FromStr;
    use test_log::test;

    use ibc_proto::ibc::core::channel::v1::Channel as RawChannel;

    use crate::core::ics04_channel::channel::test_util::get_dummy_raw_channel_end;
    use crate::core::ics04_channel::channel::ChannelEnd;

    #[test]
    fn channel_end_try_from_raw() {
        let raw_channel_end = get_dummy_raw_channel_end();

        let empty_raw_channel_end = RawChannel {
            counterparty: None,
            ..raw_channel_end.clone()
        };

        struct Test {
            name: String,
            params: RawChannel,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Raw channel end with missing counterparty".to_string(),
                params: empty_raw_channel_end,
                want_pass: false,
            },
            Test {
                name: "Raw channel end with incorrect state".to_string(),
                params: RawChannel {
                    state: -1,
                    ..raw_channel_end.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Raw channel end with incorrect ordering".to_string(),
                params: RawChannel {
                    ordering: -1,
                    ..raw_channel_end.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Raw channel end with incorrect connection id in connection hops".to_string(),
                params: RawChannel {
                    connection_hops: vec!["connection*".to_string()].into_iter().collect(),
                    ..raw_channel_end.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Raw channel end with incorrect connection id (has blank space)".to_string(),
                params: RawChannel {
                    connection_hops: vec!["con nection".to_string()].into_iter().collect(),
                    ..raw_channel_end.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Raw channel end with two correct connection ids in connection hops"
                    .to_string(),
                params: RawChannel {
                    connection_hops: vec!["connection1".to_string(), "connection2".to_string()]
                        .into_iter()
                        .collect(),
                    ..raw_channel_end.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Raw channel end with correct params".to_string(),
                params: raw_channel_end,
                want_pass: true,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let ce_result = ChannelEnd::try_from(p);

            assert_eq!(
                test.want_pass,
                ce_result.is_ok(),
                "ChannelEnd::try_from() failed for test {}, \nmsg{:?} with error {:?}",
                test.name,
                test.params.clone(),
                ce_result.err(),
            );
        }
    }

    #[test]
    fn parse_channel_ordering_type() {
        use super::Ordering;

        struct Test {
            ordering: &'static str,
            want_res: Option<Ordering>,
        }
        let tests: Vec<Test> = vec![
            Test {
                ordering: "UNINITIALIZED",
                want_res: Some(Ordering::Uninitialized),
            },
            Test {
                ordering: "UNORDERED",
                want_res: Some(Ordering::Unordered),
            },
            Test {
                ordering: "ORDERED",
                want_res: Some(Ordering::Ordered),
            },
            Test {
                ordering: "UNKNOWN_ORDER",
                want_res: None,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            match Ordering::from_str(test.ordering) {
                Ok(res) => assert_eq!(test.want_res, Some(res)),
                Err(_) => assert!(test.want_res.is_none(), "parse failed"),
            }
        }
    }

    #[test]
    fn less_or_equal_progress_uninitialized() {
        use crate::core::ics04_channel::channel::State;
        use crate::core::ics04_channel::channel::UpgradeState;

        let higher_or_equal_states = vec![
            State::Uninitialized,
            State::Init,
            State::TryOpen,
            State::Open(UpgradeState::NotUpgrading),
            State::Open(UpgradeState::Upgrading),
            State::Closed,
            State::Flushing,
            State::Flushcomplete,
        ];
        for state in higher_or_equal_states {
            assert!(State::Uninitialized.less_or_equal_progress(state))
        }
    }

    #[test]
    fn less_or_equal_progress_init() {
        use crate::core::ics04_channel::channel::State;
        use crate::core::ics04_channel::channel::UpgradeState;

        let lower_states = vec![State::Uninitialized];
        let higher_or_equal_states = vec![
            State::Init,
            State::TryOpen,
            State::Open(UpgradeState::NotUpgrading),
            State::Open(UpgradeState::Upgrading),
            State::Closed,
            State::Flushing,
            State::Flushcomplete,
        ];
        for state in lower_states {
            assert!(!State::Init.less_or_equal_progress(state));
        }
        for state in higher_or_equal_states {
            assert!(State::Init.less_or_equal_progress(state))
        }
    }

    #[test]
    fn less_or_equal_progress_tryopen() {
        use crate::core::ics04_channel::channel::State;
        use crate::core::ics04_channel::channel::UpgradeState;

        let lower_states = vec![State::Uninitialized, State::Init];
        let higher_or_equal_states = vec![
            State::TryOpen,
            State::Open(UpgradeState::NotUpgrading),
            State::Open(UpgradeState::Upgrading),
            State::Closed,
            State::Flushing,
            State::Flushcomplete,
        ];
        for state in lower_states {
            assert!(!State::TryOpen.less_or_equal_progress(state));
        }
        for state in higher_or_equal_states {
            assert!(State::TryOpen.less_or_equal_progress(state))
        }
    }

    #[test]
    fn less_or_equal_progress_open_not_upgrading() {
        use crate::core::ics04_channel::channel::State;
        use crate::core::ics04_channel::channel::UpgradeState;

        let lower_states = vec![State::Uninitialized, State::Init, State::TryOpen];
        let higher_or_equal_states = vec![
            State::Open(UpgradeState::NotUpgrading),
            State::Open(UpgradeState::Upgrading),
            State::Closed,
            State::Flushing,
            State::Flushcomplete,
        ];
        for state in lower_states {
            assert!(!State::Open(UpgradeState::NotUpgrading).less_or_equal_progress(state));
        }
        for state in higher_or_equal_states {
            assert!(State::Open(UpgradeState::NotUpgrading).less_or_equal_progress(state))
        }
    }

    #[test]
    fn less_or_equal_progress_upgrading_states() {
        use crate::core::ics04_channel::channel::State;
        use crate::core::ics04_channel::channel::UpgradeState;

        let states = [
            State::Uninitialized,
            State::Init,
            State::TryOpen,
            State::Open(UpgradeState::NotUpgrading),
            State::Open(UpgradeState::Upgrading),
            State::Closed,
            State::Flushing,
            State::Flushcomplete,
        ];

        let upgrading_states = vec![
            State::Open(UpgradeState::Upgrading),
            State::Closed,
            State::Flushing,
            State::Flushcomplete,
        ];
        for upgrade_state in upgrading_states {
            for state in states.iter() {
                assert!(!upgrade_state.less_or_equal_progress(*state));
            }
        }
    }
}
