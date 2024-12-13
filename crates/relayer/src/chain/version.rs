use core::fmt::{Display, Error as FmtError, Formatter};

use crate::chain::cosmos::version::Specs as CosmosSpecs;
use crate::chain::namada::version::Specs as NamadaSpecs;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConsensusVersion {
    Tendermint(semver::Version),
    Comet(semver::Version),
}

impl Display for ConsensusVersion {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        let consensus = match self {
            ConsensusVersion::Tendermint(ref v) => format!("Tendermint {v}"),
            ConsensusVersion::Comet(ref v) => format!("CometBFT {v}"),
        };
        write!(f, "{consensus}")
    }
}

/// Captures the version(s) specification of different modules of a network.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Specs {
    Cosmos(CosmosSpecs),
    Namada(NamadaSpecs),
}
