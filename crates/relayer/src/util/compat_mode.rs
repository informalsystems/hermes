use tracing::warn;

use tendermint::Version;

use crate::chain::version::ConsensusVersion;
use crate::config::compat_mode::CompatMode;
use crate::error::Error;

pub fn compat_mode_from_node_version(
    configured_version: &Option<CompatMode>,
    version: Version,
) -> Result<CompatMode, Error> {
    let queried_version = CompatMode::from_version(version);

    // This will prioritize the use of the CompatMode specified in Hermes configuration file
    match (configured_version, queried_version) {
        (Some(configured), Ok(queried)) if configured != &queried => {
            warn!(
                "potential `compat_mode` misconfiguration! Configured version '{configured}' does not match chain version '{queried}'. \
                Hermes will use the configured `compat_mode` version '{configured}'. \
                If this configuration is done on purpose this message can be ignored.",
            );

            Ok(*configured)
        }
        (Some(configured), _) => Ok(*configured),
        (_, Ok(queried)) => Ok(queried),
        (_, Err(e)) => Err(Error::invalid_compat_mode(e)),
    }
}

pub fn compat_mode_from_version_specs(
    configured_mode: &Option<CompatMode>,
    version: Option<ConsensusVersion>,
) -> Result<CompatMode, Error> {
    let queried_mode = match version {
        // CometBFT 0.40 uses the 0.38 RPC layout for the classical-key
        // chains tested with Hermes, including FinalizeBlock events.
        Some(ConsensusVersion::Comet(v)) if (v.major, v.minor) == (0, 40) => {
            Some(CompatMode::V0_38)
        }
        Some(ConsensusVersion::Tendermint(v) | ConsensusVersion::Comet(v)) => {
            compat_mode_from_semver(v)
        }
        None => None,
    };

    match (configured_mode, queried_mode) {
        (Some(configured), Some(queried)) if configured == &queried => Ok(queried),
        (Some(configured), Some(queried)) => {
            warn!(
                "potential `compat_mode` misconfiguration! Configured version: {configured}, chain version: {queried}. \
                Hermes will use the configured `compat_mode` version `{configured}`. \
                If this configuration is done on purpose this message can be ignored."
            );

            Ok(*configured)
        }
        (Some(configured), None) => {
            warn!(
                "Hermes could not infer the compatibility mode for this chain, \
                and will use the configured `compat_mode` version `{configured}`."
            );

            Ok(*configured)
        }
        (None, Some(queried)) => Ok(queried),
        (None, None) => {
            warn!(
                "Hermes could not infer the compatibility mode for this chain, and no `compat_mode` was configured, \
                and will use the default compatibility mode `0.37`. \
                Please consider configuring the `compat_mode` in the Hermes configuration file."
            );

            Ok(CompatMode::V0_37)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn comet_040_uses_038_rpc_dialect_with_override_preserved() {
        let comet = Some(ConsensusVersion::Comet(semver::Version::new(0, 40, 0)));
        assert_eq!(
            compat_mode_from_version_specs(&None, comet.clone()).unwrap(),
            CompatMode::V0_38
        );
        assert_eq!(
            compat_mode_from_version_specs(&Some(CompatMode::V0_37), comet).unwrap(),
            CompatMode::V0_37
        );
    }
}

fn compat_mode_from_semver(v: semver::Version) -> Option<CompatMode> {
    match (v.major, v.minor) {
        (0, 34) => Some(CompatMode::V0_34),
        (0, 37) => Some(CompatMode::V0_37),
        (0, 38) => Some(CompatMode::V0_38),
        _ => None,
    }
}
