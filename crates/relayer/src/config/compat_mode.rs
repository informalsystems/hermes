use core::{
    fmt::{
        Display,
        Error as FmtError,
        Formatter,
    },
    str::FromStr,
};

use serde::{
    Deserialize,
    Deserializer,
    Serialize,
    Serializer,
};
use tendermint_rpc::client::CompatMode as TmCompatMode;

use crate::config::Error;

/// CometBFT RPC compatibility mode
///
/// Can be removed in favor of the one in tendermint-rs, once
/// <https://github.com/informalsystems/tendermint-rs/pull/1367> is merged.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CompatMode {
    /// Use version 0.34 of the protocol.
    V0_34,
    /// Use version 0.37 of the protocol.
    V0_37,
}

impl Display for CompatMode {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match self {
            Self::V0_34 => write!(f, "v0.34"),
            Self::V0_37 => write!(f, "v0.37"),
        }
    }
}

impl FromStr for CompatMode {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        const VALID_COMPAT_MODES: &str = "0.34, 0.37";

        // Trim leading 'v', if present
        match s.trim_start_matches('v') {
            "0.34" => Ok(CompatMode::V0_34),
            "0.37" => Ok(CompatMode::V0_37),
            _ => Err(Error::invalid_compat_mode(
                s.to_string(),
                VALID_COMPAT_MODES,
            )),
        }
    }
}

impl<'de> Deserialize<'de> for CompatMode {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        use serde::de;

        let s = String::deserialize(deserializer)?;
        FromStr::from_str(&s).map_err(de::Error::custom)
    }
}

impl Serialize for CompatMode {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.to_string().serialize(serializer)
    }
}

impl From<TmCompatMode> for CompatMode {
    fn from(value: TmCompatMode) -> Self {
        match value {
            TmCompatMode::V0_34 => Self::V0_34,
            TmCompatMode::V0_37 => Self::V0_37,
        }
    }
}

impl From<CompatMode> for TmCompatMode {
    fn from(value: CompatMode) -> Self {
        match value {
            CompatMode::V0_34 => Self::V0_34,
            CompatMode::V0_37 => Self::V0_37,
        }
    }
}

impl CompatMode {
    pub fn equal_to_tm_compat_mode(&self, tm_compat_mode: TmCompatMode) -> bool {
        match self {
            Self::V0_34 => tm_compat_mode == TmCompatMode::V0_34,
            Self::V0_37 => tm_compat_mode == TmCompatMode::V0_37,
        }
    }
}
