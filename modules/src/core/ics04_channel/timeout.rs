use crate::prelude::*;

use core::fmt::Display;

use crate::{core::ics02_client::error::Error as ICS2Error, Height};

use ibc_proto::ibc::core::client::v1::Height as RawHeight;
use serde::{Deserialize, Serialize};
use tendermint::abci::tag::Value as TagValue;

/// Represents a height to be used to timeout packets.
///
/// `TimeoutHeight` is treated differently from other heights because
///
/// `RawHeight.timeout_height == {revision_number: 0, revision_height = 0}`
///
/// is legal and meaningful, even though the Tendermint spec rejects this
/// height as invalid. Thus, it must be parsed specially, where this
/// special case means "no timeout".
#[derive(Clone, Copy, Debug, Default, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct TimeoutHeight(Option<Height>);

impl TimeoutHeight {
    pub fn no_timeout() -> Self {
        Self(None)
    }

    /// Revision number to be used in packet commitment computation
    pub fn commitment_revision_number(&self) -> u64 {
        match self.0 {
            Some(height) => height.revision_number(),
            None => 0,
        }
    }

    /// Revision height to be used in packet commitment computation
    pub fn commitment_revision_height(&self) -> u64 {
        match self.0 {
            Some(height) => height.revision_height(),
            None => 0,
        }
    }

    /// Check if a height is past the timeout height, and thus is expired.
    pub fn has_expired(&self, height: &Height) -> bool {
        match self.0 {
            Some(timeout_height) => *height >= timeout_height,
            // When there's no timeout, heights are never expired
            None => false,
        }
    }

    // FIXME: Find better name
    pub fn has_timeout(&self) -> bool {
        self.0.is_some()
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
            Ok(TimeoutHeight(None))
        } else {
            let height: Height = raw_height.try_into()?;
            Ok(TimeoutHeight(Some(height)))
        }
    }
}

impl TryFrom<Option<RawHeight>> for TimeoutHeight {
    type Error = ICS2Error;

    fn try_from(maybe_raw_height: Option<RawHeight>) -> Result<Self, Self::Error> {
        match maybe_raw_height {
            Some(raw_height) => Self::try_from(raw_height),
            None => Ok(TimeoutHeight(None)),
        }
    }
}
/// We map "no timeout height" to `Some(RawHeight::zero)` due to a quirk
/// in ICS-4. See <https://github.com/cosmos/ibc/issues/776>.
impl From<TimeoutHeight> for Option<RawHeight> {
    fn from(timeout_height: TimeoutHeight) -> Self {
        let raw_height = match timeout_height.0 {
            Some(height) => height.into(),
            None => RawHeight {
                revision_number: 0,
                revision_height: 0,
            },
        };

        Some(raw_height)
    }
}

impl From<Height> for TimeoutHeight {
    fn from(height: Height) -> Self {
        Self(Some(height))
    }
}

impl From<TimeoutHeight> for TagValue {
    fn from(timeout_height: TimeoutHeight) -> Self {
        match timeout_height.0 {
            Some(height) => height.to_string().parse().unwrap(),
            None => "0-0".parse().unwrap(),
        }
    }
}

impl Display for TimeoutHeight {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.0 {
            Some(timeout_height) => write!(f, "{}", timeout_height),
            None => write!(f, "no timeout"),
        }
    }
}
