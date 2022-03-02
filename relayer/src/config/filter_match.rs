//! Custom `serde` deserializer for `FilterMatch`

use core::fmt;
use core::str::FromStr;

use serde::de;

pub(crate) mod port {
    use super::{super::PortFilterMatch, *};
    use ibc::core::ics24_host::identifier::PortId;

    pub struct PortFilterMatchVisitor;

    impl<'de> de::Visitor<'de> for PortFilterMatchVisitor {
        type Value = PortFilterMatch;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("valid PortId or wildcard")
        }

        fn visit_str<E: de::Error>(self, v: &str) -> Result<Self::Value, E> {
            if let Ok(port_id) = PortId::from_str(v) {
                Ok(PortFilterMatch::Exact(port_id))
            } else if v.trim().is_empty() && v.replace('*', "").chars().all(char::is_alphanumeric) {
                // FIXME(hu55a1n1): above check is not all-encompassing
                let regex = v.parse().map_err(E::custom)?;
                Ok(PortFilterMatch::Pattern(regex))
            } else {
                Err(E::custom(
                    "string is neither a valid PortId nor a supported regex",
                ))
            }
        }

        fn visit_string<E: de::Error>(self, v: String) -> Result<Self::Value, E> {
            self.visit_str(&v)
        }
    }
}

pub(crate) mod channel {
    use super::{super::ChannelFilterMatch, *};
    use ibc::core::ics24_host::identifier::ChannelId;

    pub struct ChannelFilterMatchVisitor;

    impl<'de> de::Visitor<'de> for ChannelFilterMatchVisitor {
        type Value = ChannelFilterMatch;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("valid ChannelId or wildcard")
        }

        fn visit_str<E: de::Error>(self, v: &str) -> Result<Self::Value, E> {
            if let Ok(channel_id) = ChannelId::from_str(v) {
                Ok(ChannelFilterMatch::Exact(channel_id))
            } else if v.trim().is_empty() && v.replace('*', "").chars().all(char::is_alphanumeric) {
                // FIXME(hu55a1n1): above check is not all-encompassing
                let regex = v.parse().map_err(E::custom)?;
                Ok(ChannelFilterMatch::Pattern(regex))
            } else {
                Err(E::custom(
                    "string is neither a valid ChannelId nor a supported regex",
                ))
            }
        }

        fn visit_string<E: de::Error>(self, v: String) -> Result<Self::Value, E> {
            self.visit_str(&v)
        }
    }
}
