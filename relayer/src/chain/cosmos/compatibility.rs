//! Cosmos-SDK compatibility constants and helper methods.

use thiserror::Error;

use ibc_proto::cosmos::base::tendermint::v1beta1::VersionInfo;

/// Specifies the SDK & IBC-go modules path, as it is expected
/// to appear in the application version information.
///
/// The module identification is captured in a [`Module`]
/// with the following structure as an example:
/// ```json,ignore
/// Module {
///    path: "github.com/cosmos/cosmos-sdk",
///    version: "v0.42.4",
///    sum: "h1:yaD4PyOx0LnyfiWasC5egg1U76lT83GRxjJjupPo7Gk=",
/// },
/// ```
const SDK_MODULE_NAME: &str = "cosmos/cosmos-sdk";
const IBC_GO_MODULE_NAME: &str = "cosmos/ibc-go";

/// Specifies the SDK module version requirement.
///
/// # Note: Should be consistent with [features] guide page.
///
/// [features]: https://hermes.informal.systems/features.html
const SDK_MODULE_VERSION_REQ: &str = ">=0.41, <0.45";

/// Specifies the IBC-go module version requirement.
/// At the moment, we support both chains with and without
/// the standalone ibc-go module, i.e., it's not an error
/// if the chain binary does not build with this module.
///
/// # Note: Should be consistent with [features] guide page.
///
/// [features]: https://hermes.informal.systems/features.html
const IBC_GO_MODULE_VERSION_REQ: &str = ">=1.1, <1.2";

/// Helper struct to capture all the reported information of an
/// IBC application, e.g., `gaiad`.
#[derive(Clone, Debug)]
pub struct AppInfo {
    app_name: String,
    version: String,
    git_commit: String,
}

impl core::fmt::Display for AppInfo {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}:{}-{}", self.app_name, self.version, self.git_commit)
    }
}

impl From<&VersionInfo> for AppInfo {
    fn from(vi: &VersionInfo) -> Self {
        Self {
            app_name: vi.app_name.clone(),
            version: vi.version.clone(),
            git_commit: vi.git_commit.clone(),
        }
    }
}

impl From<VersionInfo> for AppInfo {
    fn from(vi: VersionInfo) -> Self {
        Self {
            app_name: vi.app_name,
            version: vi.version,
            git_commit: vi.git_commit,
        }
    }
}

#[derive(Error, Debug)]
pub enum Diagnostic {
    #[error("no SDK module '{pattern}' was found for application {app}")]
    SdkModuleNotFound { pattern: String, app: AppInfo },

    #[error("failed parsing the SDK module ('{module_path}') version number '{raw_version}' into a semver for application {app}; cause: {cause}")]
    VersionParsingFailed {
        module_path: String,
        raw_version: String,
        cause: String,
        app: AppInfo,
    },

    #[error("SDK module at version '{found}' does not meet compatibility requirements {requirements} for application {app}")]
    MismatchingSdkModuleVersion {
        requirements: String,
        found: String,
        app: AppInfo,
    },

    #[error("Ibc-Go module at version '{found}' does not meet compatibility requirements {requirements} for application {app}")]
    MismatchingIbcGoModuleVersion {
        requirements: String,
        found: String,
        app: AppInfo,
    },
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
pub(crate) fn run_diagnostic(v: VersionInfo) -> Result<(), Diagnostic> {
    sdk_diagnostic(v.clone())?;
    ibc_go_diagnostic(v)?;
    Ok(())
}

fn sdk_diagnostic(v: VersionInfo) -> Result<(), Diagnostic> {
    // Parse the SDK requirements into a semver
    let sdk_reqs = semver::VersionReq::parse(SDK_MODULE_VERSION_REQ)
        .expect("parsing the SDK module requirements into semver");

    // Get the Cosmos SDK version
    let mut version = get_sdk_version(&v)?;

    // Remove the pre-release version to ensure we treat pre-releases of the SDK
    // as their normal version, eg. 0.42.0-rc2 should satisfy >=0.41.3, <= 0.42.6.
    version.pre = semver::Prerelease::EMPTY;

    // Finally, check the version requirements
    match sdk_reqs.matches(&version) {
        true => Ok(()),
        false => Err(Diagnostic::MismatchingSdkModuleVersion {
            requirements: SDK_MODULE_VERSION_REQ.to_string(),
            found: version.to_string(),
            app: AppInfo::from(v),
        }),
    }
}

fn get_sdk_version(version_info: &VersionInfo) -> Result<semver::Version, Diagnostic> {
    let module = version_info
        .build_deps
        .iter()
        .find(|&m| m.path.contains(SDK_MODULE_NAME))
        .ok_or_else(|| Diagnostic::SdkModuleNotFound {
            pattern: SDK_MODULE_NAME.to_string(),
            app: AppInfo::from(version_info),
        })?;

    // The raw version number has a leading 'v', trim it out;
    let plain_version = module.version.trim_start_matches('v');

    // Parse the module version
    let version =
        semver::Version::parse(plain_version).map_err(|e| Diagnostic::VersionParsingFailed {
            module_path: module.path.clone(),
            raw_version: module.version.clone(),
            cause: e.to_string(),
            app: AppInfo::from(version_info),
        })?;

    Ok(version)
}

fn ibc_go_diagnostic(version_info: VersionInfo) -> Result<(), Diagnostic> {
    // Parse the IBC-go module requirements into a semver
    let ibc_reqs = semver::VersionReq::parse(IBC_GO_MODULE_VERSION_REQ)
        .expect("parsing the IBC-Go module requirements into semver");

    // Find the Ibc-Go module
    match version_info
        .build_deps
        .iter()
        .find(|&m| m.path.contains(IBC_GO_MODULE_NAME))
    {
        // If binary lacks the ibc-go dependency it is _not_ an error,
        // we support chains without the standalone ibc-go module.
        None => Ok(()),
        Some(ibc_module) => {
            // The raw version number has a leading 'v', trim it out;
            let plain_version = ibc_module.version.trim_start_matches('v');

            // Parse the module version
            match semver::Version::parse(plain_version).map_err(|e| {
                Diagnostic::VersionParsingFailed {
                    module_path: ibc_module.path.clone(),
                    raw_version: ibc_module.version.clone(),
                    cause: e.to_string(),
                    app: AppInfo::from(version_info.clone()),
                }
            }) {
                // Check the IBC-Go version requirements
                Ok(v) => match ibc_reqs.matches(&v) {
                    true => Ok(()),
                    false => Err(Diagnostic::MismatchingIbcGoModuleVersion {
                        requirements: IBC_GO_MODULE_VERSION_REQ.to_string(),
                        found: v.to_string(),
                        app: AppInfo::from(version_info),
                    }),
                },
                Err(d) => Err(d),
            }
        }
    }
}
