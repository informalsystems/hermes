// FIXME: Remove Unknown variant and use FromStr instead of ad-hoc method?

/// Type of the consensus algorithm
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ClientType {
    Tendermint = 1,
    Unknown = 0,
}

impl ClientType {
    /// Yields the identifier of this client type as a string
    pub fn as_string(&self) -> &'static str {
        match self {
            Self::Tendermint => "tendermint",
            Self::Unknown => "",
        }
    }

    pub fn from_str(s: &str) -> Self {
        match s {
            "tendermint" => Self::Tendermint,
            _ => Self::Unknown,
        }
    }

    pub fn is_known(&self) -> bool {
        *self != Self::Unknown
    }
}
