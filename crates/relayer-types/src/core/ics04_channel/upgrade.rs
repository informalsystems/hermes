use ibc_proto::ibc::core::channel::v1::Upgrade as RawUpgrade;
use ibc_proto::Protobuf;

use crate::core::ics04_channel::error::Error as ChannelError;
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics04_channel::timeout::UpgradeTimeout;
use crate::core::ics04_channel::upgrade_fields::UpgradeFields;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Upgrade {
    pub fields: UpgradeFields,
    // timeout can be zero, see `TryFrom<RawUpgrade>` implementation
    pub timeout: Option<UpgradeTimeout>,
    pub latest_sequence_send: Sequence,
}

impl Protobuf<RawUpgrade> for Upgrade {}

impl TryFrom<RawUpgrade> for Upgrade {
    type Error = ChannelError;

    fn try_from(value: RawUpgrade) -> Result<Self, Self::Error> {
        let fields = value
            .fields
            .ok_or(ChannelError::missing_upgrade_fields())?
            .try_into()?;
        let timeout = value
            .timeout
            .filter(|tm| UpgradeTimeout::try_from(tm.clone()).is_ok())
            .map(|tm| UpgradeTimeout::try_from(tm).unwrap());
        let latest_sequence_send = value.latest_sequence_send.into();

        Ok(Self {
            fields,
            timeout,
            latest_sequence_send,
        })
    }
}

impl From<Upgrade> for RawUpgrade {
    fn from(value: Upgrade) -> Self {
        let timeout = value.timeout.map(|tm| tm.into());
        Self {
            fields: Some(value.fields.into()),
            timeout,
            latest_sequence_send: value.latest_sequence_send.into(),
        }
    }
}

#[cfg(test)]
pub mod test_util {
    use crate::core::ics04_channel::{
        timeout::test_util::get_dummy_upgrade_timeout,
        upgrade_fields::test_util::get_dummy_upgrade_fields,
    };
    use ibc_proto::ibc::core::channel::v1::Upgrade as RawUpgrade;

    pub fn get_dummy_upgrade() -> RawUpgrade {
        RawUpgrade {
            fields: Some(get_dummy_upgrade_fields()),
            timeout: Some(get_dummy_upgrade_timeout()),
            latest_sequence_send: 1,
        }
    }
}
