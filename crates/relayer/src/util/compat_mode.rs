use tendermint::Version;
use tendermint_rpc::client::CompatMode as TmCompatMode;
use tracing::warn;

use crate::{
    config::compat_mode::CompatMode,
    error::Error,
};

/// This is a wrapper around tendermint-rs CompatMode::from_version() method.
///
pub fn compat_mode_from_version(
    configured_version: &Option<CompatMode>,
    version: Version,
) -> Result<CompatMode, Error> {
    let queried_version = TmCompatMode::from_version(version);

    // This will prioritize the use of the CompatMode specified in Hermes configuration file
    match (configured_version, queried_version) {
        (Some(configured), Ok(queried)) if !configured.equal_to_tm_compat_mode(queried) => {
            warn!("be wary of potential `compat_mode` misconfiguration. Configured version: {}, chain version: {}. Hermes will use the configured `compat_mode` version `{}`. If this configuration is done on purpose this message can be ignored.", configured, queried, configured);
            Ok(configured.clone())
        }
        (Some(configured), _) => Ok(configured.clone()),
        (_, Ok(queried)) => Ok(queried.into()),
        (_, Err(e)) => Err(Error::invalid_compat_mode(e)),
    }
}
