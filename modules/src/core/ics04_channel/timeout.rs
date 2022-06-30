use crate::prelude::*;

use core::fmt::Display;

use crate::{core::ics02_client::error::Error as ICS2Error, Height};

use ibc_proto::ibc::core::client::v1::Height as RawHeight;
use serde::{Deserialize, Serialize};
use tendermint::abci::tag::Value as TagValue;

/// Indicates a consensus height on the destination chain after which the packet
/// will no longer be processed, and will instead count as having timed-out.
///
/// `TimeoutHeight` is treated differently from other heights because
///
/// `RawHeight.timeout_height == {revision_number: 0, revision_height = 0}`
///
/// is legal and meaningful, even though the Tendermint spec rejects this height
/// as invalid. Thus, it must be parsed specially, where this special case means
/// "no timeout".
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub enum TimeoutHeight {
    Never,
    At(Height),
}

impl TimeoutHeight {
    pub fn no_timeout() -> Self {
        Self::Never
    }

    /// Revision number to be used in packet commitment computation
    pub fn commitment_revision_number(&self) -> u64 {
        match self {
            Self::At(height) => height.revision_number(),
            Self::Never => 0,
        }
    }

    /// Revision height to be used in packet commitment computation
    pub fn commitment_revision_height(&self) -> u64 {
        match self {
            Self::At(height) => height.revision_height(),
            Self::Never => 0,
        }
    }

    /// Check if a height is *stricly past* the timeout height, and thus is
    /// deemed expired.
    pub fn has_expired(&self, height: Height) -> bool {
        match self {
            Self::At(timeout_height) => height > *timeout_height,
            // When there's no timeout, heights are never expired
            Self::Never => false,
        }
    }
}

impl Default for TimeoutHeight {
    fn default() -> Self {
        Self::Never
    }
}

impl TryFrom<RawHeight> for TimeoutHeight {
    type Error = ICS2Error;

    // Note: it is important for `revision_number` to also be `0`, otherwise
    // packet commitment proofs will be incorrect (proof construction in
    // `ChannelReader::packet_commitment()` uses both `revision_number` and
    // `revision_height`). Note also that ibc-go conforms to this convention.
    fn try_from(raw_height: RawHeight) -> Result<Self, Self::Error> {
        if raw_height.revision_number == 0 && raw_height.revision_height == 0 {
            Ok(TimeoutHeight::Never)
        } else {
            let height: Height = raw_height.try_into()?;
            Ok(TimeoutHeight::At(height))
        }
    }
}

impl TryFrom<Option<RawHeight>> for TimeoutHeight {
    type Error = ICS2Error;

    fn try_from(maybe_raw_height: Option<RawHeight>) -> Result<Self, Self::Error> {
        match maybe_raw_height {
            Some(raw_height) => Self::try_from(raw_height),
            None => Ok(TimeoutHeight::Never),
        }
    }
}
/// We map "no timeout height" to `Some(RawHeight::zero)` due to a quirk
/// in ICS-4. See <https://github.com/cosmos/ibc/issues/776>.
impl From<TimeoutHeight> for Option<RawHeight> {
    fn from(timeout_height: TimeoutHeight) -> Self {
        let raw_height = match timeout_height {
            TimeoutHeight::At(height) => height.into(),
            TimeoutHeight::Never => RawHeight {
                revision_number: 0,
                revision_height: 0,
            },
        };

        Some(raw_height)
    }
}

impl From<Height> for TimeoutHeight {
    fn from(height: Height) -> Self {
        Self::At(height)
    }
}

impl From<TimeoutHeight> for TagValue {
    fn from(timeout_height: TimeoutHeight) -> Self {
        match timeout_height {
            TimeoutHeight::At(height) => height.to_string().parse().unwrap(),
            TimeoutHeight::Never => "0-0".parse().unwrap(),
        }
    }
}

impl Display for TimeoutHeight {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TimeoutHeight::At(timeout_height) => write!(f, "{}", timeout_height),
            TimeoutHeight::Never => write!(f, "no timeout"),
        }
    }
}
