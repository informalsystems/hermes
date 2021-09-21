//! Cosmos-SDK compatibility constants and helper methods.

use thiserror::Error;

use ibc_proto::cosmos::base::tendermint::v1beta1::VersionInfo;

/// Specifies the SDK module path, as it is expected to appear
/// in the application version information.
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

/// Specifies the SDK module version requirement.
///
/// # Note: Should be consistent with [features] guide page.
///
/// [features]: https://hermes.informal.systems/features.html
const SDK_MODULE_VERSION_REQ: &str = ">=0.41.3, <=0.44.0";

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
}

/// Runs a diagnostic check on the provided [`VersionInfo`]
/// to ensure that the Sdk module version matches the
/// predefined requirements.
///
/// Returns `None` upon success, or a [`Diagnostic`] upon
/// an error.
///
/// Relies on the constant [`SDK_MODULE_NAME`] to find the
/// Sdk module by name, as well as the constant
/// [`SDK_MODULE_VERSION_REQ`] for version compatibility
/// requirements.
pub(crate) fn run_diagnostic(version_info: VersionInfo) -> Result<(), Diagnostic> {
    // Parse the requirements into a semver
    let reqs = semver::VersionReq::parse(SDK_MODULE_VERSION_REQ)
        .expect("parsing the SDK module requirements into semver");

    // Get the Cosmos SDK version
    let mut version = get_sdk_version(&version_info)?;

    // Remove the pre-release version to ensure we treat pre-releases of the SDK
    // as their normal version, eg. 0.42.0-rc2 should satisfy >=0.41.3, <= 0.42.6.
    version.pre = semver::Prerelease::EMPTY;

    // Finally, check the version requirements
    match reqs.matches(&version) {
        true => Ok(()),
        false => Err(Diagnostic::MismatchingSdkModuleVersion {
            requirements: SDK_MODULE_VERSION_REQ.to_string(),
            found: version.to_string(),
            app: AppInfo::from(version_info),
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
