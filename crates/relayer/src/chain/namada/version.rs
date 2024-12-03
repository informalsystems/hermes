use core::fmt::{Display, Error as FmtError, Formatter};

use crate::chain::version::ConsensusVersion;

/// Captures the version(s) specification of different modules of a network.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Specs {
    pub namada: Option<semver::Version>,
    pub consensus: Option<ConsensusVersion>,
}

impl Display for Specs {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        let namada = self
            .namada
            .as_ref()
            .map(|v| v.to_string())
            .unwrap_or_else(|| "UNKNOWN".to_string());

        let consensus = match self.consensus {
            Some(ref v) => v.to_string(),
            None => "Tendermint: UNKNOWN, CometBFT: UNKNOWN".to_string(),
        };

        write!(f, "Namada {}, {}", namada, consensus)
    }
}
