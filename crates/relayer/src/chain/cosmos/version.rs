//! Utilities for extracting and parsing versioning information
//! of Cosmos-SDK networks. The extracted version specification
//! is captured in a domain-type semver format in [`Specs`].

use core::fmt::{Display, Error as FmtError, Formatter};

use flex_error::define_error;
use tracing::trace;

use ibc_proto::cosmos::base::tendermint::v1beta1::VersionInfo;

/// Specifies the SDK, IBC-go, and Tendermint modules path, as expected
/// to appear in the application version information of a
/// Cosmos-SDK network.
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
const SDK_MODULE_NAME: &str = "github.com/cosmos/cosmos-sdk";
const IBC_GO_MODULE_NAME: &str = "github.com/cosmos/ibc-go";
const TENDERMINT_MODULE_NAME: &str = "github.com/tendermint/tendermint";
const COMET_MODULE_NAME: &str = "github.com/cometbft/cometbft";

/// Captures the version(s) specification of different modules of a network.
#[derive(Debug)]
pub struct Specs {
    pub cosmos_sdk: Option<semver::Version>,
    pub ibc_go: Option<semver::Version>,
    pub tendermint: Option<semver::Version>,
    pub comet: Option<semver::Version>,
}

impl Display for Specs {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        let cosmos_sdk = self
            .cosmos_sdk
            .as_ref()
            .map(|v| v.to_string())
            .unwrap_or_else(|| "UNKNOWN".to_string());

        let ibc_go = self
            .ibc_go
            .as_ref()
            .map(|v| v.to_string())
            .unwrap_or_else(|| "UNKNOWN".to_string());

        let tendermint = self
            .tendermint
            .as_ref()
            .map(|v| v.to_string())
            .unwrap_or_else(|| "UNKNOWN".to_string());

        let comet = self
            .comet
            .as_ref()
            .map(|v| v.to_string())
            .unwrap_or_else(|| "UNKNOWN".to_string());

        write!(
            f,
            "Cosmos SDK {}, IBC-Go {}, Tendermint {}, CometBFT {}",
            cosmos_sdk, ibc_go, tendermint, comet
        )
    }
}

define_error! {
    Error {
        ConsensusModuleNotFound
            {
                tendermint: String,
                comet: String,
                app: AppInfo,
            }
            |e| { format!("failed to find the Tendermint ('{}') or CometBFT ('{}') dependency for application {}", e.tendermint, e.comet, e.app) },

        VersionParsingFailed
            {
                module_path: String,
                raw_version: String,
                cause: String,
                app: AppInfo,
            }
            |e| { format!("failed parsing the module path ('{}') version number '{}' into a semver for application {}; cause: {}",
                    e.module_path, e.raw_version, e.app, e.cause) },
    }
}

impl TryFrom<VersionInfo> for Specs {
    type Error = Error;

    fn try_from(raw_version: VersionInfo) -> Result<Self, Self::Error> {
        // Get the Cosmos SDK version
        let sdk_version = parse_sdk_version(&raw_version)?;
        let ibc_go_version = parse_ibc_go_version(&raw_version)?;
        let tendermint_version = parse_tendermint_version(&raw_version)?;
        let comet_version = parse_comet_version(&raw_version)?;

        // Ensure that either Tendermint or CometBFT are being used.
        if tendermint_version.is_none() && comet_version.is_none() {
            return Err(Error::consensus_module_not_found(
                TENDERMINT_MODULE_NAME.to_string(),
                COMET_MODULE_NAME.to_string(),
                AppInfo::from(&raw_version),
            ));
        };

        trace!(
            application = %raw_version.app_name,
            version = %raw_version.version,
            git_commit = %raw_version.git_commit,
            sdk_version = ?sdk_version,
            ibc_go_status = ?ibc_go_version,
            tendermint_version = ?tendermint_version,
            comet_version = ?comet_version,
            "parsed version specification"
        );

        Ok(Self {
            cosmos_sdk: sdk_version,
            ibc_go: ibc_go_version,
            tendermint: tendermint_version,
            comet: comet_version,
        })
    }
}

fn parse_sdk_version(version_info: &VersionInfo) -> Result<Option<semver::Version>, Error> {
    parse_optional_version(version_info, SDK_MODULE_NAME)
}

fn parse_ibc_go_version(version_info: &VersionInfo) -> Result<Option<semver::Version>, Error> {
    parse_optional_version(version_info, IBC_GO_MODULE_NAME)
}

fn parse_tendermint_version(version_info: &VersionInfo) -> Result<Option<semver::Version>, Error> {
    parse_optional_version(version_info, TENDERMINT_MODULE_NAME)
}

fn parse_comet_version(version_info: &VersionInfo) -> Result<Option<semver::Version>, Error> {
    parse_optional_version(version_info, COMET_MODULE_NAME)
}

fn parse_optional_version(
    version_info: &VersionInfo,
    module_name: &str,
) -> Result<Option<semver::Version>, Error> {
    match version_info
        .build_deps
        .iter()
        .find(|&m| m.path == module_name)
    {
        None => Ok(None),
        Some(module) => {
            let plain_version = module.version.trim_start_matches('v');

            semver::Version::parse(plain_version)
                .map(|mut version| {
                    version.pre = semver::Prerelease::EMPTY;
                    Some(version)
                })
                .map_err(|e| {
                    Error::version_parsing_failed(
                        module.path.clone(),
                        module.version.clone(),
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

impl Display for AppInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
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
