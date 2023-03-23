//! Cosmos-SDK compatibility constants and diagnostic methods.

use thiserror::Error;
use tracing::debug;

use super::version;

/// Specifies the SDK module version requirement.
///
/// # Note: Should be consistent with [features] guide page.
///
/// [features]: https://hermes.informal.systems/advanced/features.html
const SDK_MODULE_VERSION_REQ: &str = ">=0.44, <0.48";

/// Specifies the IBC-go module version requirement.
/// At the moment, we support both chains with and without
/// the standalone ibc-go module, i.e., it's not an error
/// if the chain binary does not build with this module.
///
/// # Note: Should be consistent with [features] guide page.
///
/// [features]: https://hermes.informal.systems/advanced/features.html
const IBC_GO_MODULE_VERSION_REQ: &str = ">=1.1, <=7";

#[derive(Error, Debug)]
pub enum Diagnostic {
    #[error(
        "SDK module at version '{found}' does not meet compatibility requirements {requirements}"
    )]
    MismatchingSdkModuleVersion { requirements: String, found: String },

    #[error("Ibc-Go module at version '{found}' does not meet compatibility requirements {requirements}")]
    MismatchingIbcGoModuleVersion { requirements: String, found: String },
}

/// Runs a diagnostic check on the provided [`VersionInfo`]
/// to ensure that the Sdk & IBC-go modules version match
/// the predefined requirements.
///
/// Returns `None` upon success, or a [`Diagnostic`] upon
/// an error.
///
/// Relies on the constant [`SDK_MODULE_NAME`] to find the
/// Sdk module by name, as well as the constants
/// [`SDK_MODULE_VERSION_REQ`] and [`IBC_GO_MODULE_VERSION_REQ`]
/// for establishing compatibility requirements.
pub(crate) fn run_diagnostic(v: &version::Specs) -> Result<(), Diagnostic> {
    debug!("running diagnostic on version info {}", v);

    sdk_diagnostic(&v.cosmos_sdk)?;
    ibc_go_diagnostic(v.ibc_go.as_ref())?;

    Ok(())
}

fn sdk_diagnostic(version: &semver::Version) -> Result<(), Diagnostic> {
    // Parse the SDK requirements into a semver
    let sdk_reqs = semver::VersionReq::parse(SDK_MODULE_VERSION_REQ)
        .expect("parsing the SDK module requirements into semver");

    // Finally, check the version requirements
    match sdk_reqs.matches(version) {
        true => Ok(()),
        false => Err(Diagnostic::MismatchingSdkModuleVersion {
            requirements: SDK_MODULE_VERSION_REQ.to_string(),
            found: version.to_string(),
        }),
    }
}

fn ibc_go_diagnostic(version_info: Option<&semver::Version>) -> Result<(), Diagnostic> {
    // Parse the IBC-go module requirements into a semver
    let ibc_reqs = semver::VersionReq::parse(IBC_GO_MODULE_VERSION_REQ)
        .expect("parsing the IBC-Go module requirements into semver");

    // Find the Ibc-Go module
    match version_info {
        // If binary lacks the ibc-go dependency it is _not_ an error,
        // we support chains without the standalone ibc-go module.
        None => Ok(()),
        Some(version) => match ibc_reqs.matches(version) {
            true => Ok(()),
            false => Err(Diagnostic::MismatchingIbcGoModuleVersion {
                requirements: IBC_GO_MODULE_VERSION_REQ.to_string(),
                found: version.to_string(),
            }),
        },
    }
}
