//! Utilities for extracting and parsing versioning information
//! of Cosmos-SDK chains. The extracted version specification
//! is captured in a domain-type semver format in [`Specs`].

use flex_error::define_error;
use tracing::trace;

use ibc_proto::cosmos::base::tendermint::v1beta1::VersionInfo;

/// Specifies the SDK & IBC-go modules path, as it is expected
/// to appear in the application version information of a
/// Cosmos chain.
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

/// Captures the version(s) specification of different
/// modules of a chain.
///
/// Assumes that the chain runs on Cosmos SDK.
/// Stores both the SDK version as well as
/// the IBC-go module version (if existing).
pub struct Specs {
    pub sdk_version: semver::Version,
    pub ibc_go_version: Option<semver::Version>,
}

define_error! {
    Error {
        SdkModuleNotFound
            {
                address: String,
                app: AppInfo,
            }
            |e| { format!("node at {} running chain {} not caught up", e.address, e.app) },

        VersionParsingFailed
            {
                module_path: String,
                raw_version: String,
                cause: String,
                app: AppInfo,
            }
            |e| { format!("failed parsing the SDK module ('{}') version number '{}' into a semver for application {}; cause: {}",
                    e.module_path, e.raw_version, e.app, e.cause) },
    }
}

impl TryFrom<VersionInfo> for Specs {
    type Error = Error;

    fn try_from(raw_version: VersionInfo) -> Result<Self, Self::Error> {
        // Get the Cosmos SDK version
        let sdk_version = parse_sdk_version(&raw_version)?;
        let ibc_go_version = parse_ibc_go_version(&raw_version)?;

        trace!(
            "parsed version specification for {} {}@{} -> SDK={}; Ibc-Go status={:?}",
            raw_version.app_name,
            raw_version.version,
            raw_version.git_commit,
            sdk_version,
            ibc_go_version
        );

        Ok(Self {
            sdk_version,
            ibc_go_version,
        })
    }
}

fn parse_sdk_version(version_info: &VersionInfo) -> Result<semver::Version, Error> {
    let module = version_info
        .build_deps
        .iter()
        .find(|&m| m.path.contains(SDK_MODULE_NAME))
        .ok_or_else(|| {
            Error::sdk_module_not_found(SDK_MODULE_NAME.to_string(), AppInfo::from(version_info))
        })?;

    // The raw version number has a leading 'v', trim it out;
    let plain_version = module.version.trim_start_matches('v');

    // Parse the module version
    let mut version = semver::Version::parse(plain_version).map_err(|e| {
        Error::version_parsing_failed(
            module.path.clone(),
            module.version.clone(),
            e.to_string(),
            AppInfo::from(version_info),
        )
    })?;

    // Remove the pre-release version to ensure we treat pre-releases of the SDK
    // as their normal version, eg. 0.42.0-rc2 should satisfy >=0.41.3, <= 0.42.6.
    version.pre = semver::Prerelease::EMPTY;

    Ok(version)
}

fn parse_ibc_go_version(version_info: &VersionInfo) -> Result<Option<semver::Version>, Error> {
    // Find the Ibc-Go module
    match version_info
        .build_deps
        .iter()
        .find(|&m| m.path.contains(IBC_GO_MODULE_NAME))
    {
        // If binary lacks the ibc-go dependency it is _not_ an error,
        // we support chains without the standalone ibc-go module.
        None => Ok(None),
        Some(ibc_module) => {
            // The raw version number has a leading 'v', trim it out;
            let plain_version = ibc_module.version.trim_start_matches('v');

            // Parse the Ibc-Go module version
            semver::Version::parse(plain_version)
                .map(|mut version| {
                    // Remove the pre-release identifier from the semver
                    version.pre = semver::Prerelease::EMPTY;
                    Some(version)
                })
                .map_err(|e| {
                    Error::version_parsing_failed(
                        ibc_module.path.clone(),
                        ibc_module.version.clone(),
                        e.to_string(),
                        AppInfo::from(version_info),
                    )
                })
        }
    }
}

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
