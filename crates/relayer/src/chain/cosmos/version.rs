//! Utilities for extracting and parsing versioning information
//! of Cosmos-SDK networks. The extracted version specification
//! is captured in a domain-type semver format in [`Specs`].

use core::fmt::{Display, Error as FmtError, Formatter};

use flex_error::define_error;
use tracing::trace;

use ibc_proto::cosmos::base::tendermint::v1beta1::{Module, VersionInfo};

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
const IBC_GO_MODULE_PREFIX: &str = "github.com/cosmos/ibc-go/v";
const TENDERMINT_MODULE_NAME: &str = "github.com/tendermint/tendermint";
const COMET_MODULE_NAME: &str = "github.com/cometbft/cometbft";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConsensusVersion {
    Tendermint(semver::Version),
    Comet(semver::Version),
}

/// Captures the version(s) specification of different modules of a network.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Specs {
    pub cosmos_sdk: Option<semver::Version>,
    pub ibc_go: Option<semver::Version>,
    pub consensus: Option<ConsensusVersion>,
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

        let consensus = match self.consensus {
            Some(ConsensusVersion::Tendermint(ref v)) => format!("Tendermint {v}"),
            Some(ConsensusVersion::Comet(ref v)) => format!("CometBFT {v}"),
            None => "Tendermint: UNKNOWN, CometBFT: UNKNOWN".to_string(),
        };

        write!(
            f,
            "Cosmos SDK {}, IBC-Go {}, {}",
            cosmos_sdk, ibc_go, consensus
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
            |e| { format!("failed to find the Tendermint ('{}') or CometBFT ('{}') dependency for application {}",
                e.tendermint, e.comet, e.app) },

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

        let consensus_version = match (tendermint_version, comet_version) {
            (_, Some(comet)) => Some(ConsensusVersion::Comet(comet)),
            (Some(tendermint), _) => Some(ConsensusVersion::Tendermint(tendermint)),
            _ => None,
        };

        // Ensure that either Tendermint or CometBFT are being used.
        if consensus_version.is_none() {
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
            consensus_version = ?consensus_version,
            "parsed version specification"
        );

        Ok(Self {
            cosmos_sdk: sdk_version,
            ibc_go: ibc_go_version,
            consensus: consensus_version,
        })
    }
}

fn parse_sdk_version(version_info: &VersionInfo) -> Result<Option<semver::Version>, Error> {
    parse_optional_version(version_info, |m| m.path == SDK_MODULE_NAME)
}

fn parse_ibc_go_version(version_info: &VersionInfo) -> Result<Option<semver::Version>, Error> {
    parse_optional_version(version_info, |m| m.path.starts_with(IBC_GO_MODULE_PREFIX))
}

fn parse_tendermint_version(version_info: &VersionInfo) -> Result<Option<semver::Version>, Error> {
    parse_optional_version(version_info, |m| m.path == TENDERMINT_MODULE_NAME)
}

fn parse_comet_version(version_info: &VersionInfo) -> Result<Option<semver::Version>, Error> {
    parse_optional_version(version_info, |m| m.path == COMET_MODULE_NAME)
}

fn parse_optional_version(
    version_info: &VersionInfo,
    predicate: impl Fn(&Module) -> bool,
) -> Result<Option<semver::Version>, Error> {
    let module = version_info.build_deps.iter().find(|&m| predicate(m));

    match module {
        None => Ok(None),

        Some(module) => {
            let plain_version = module.version.trim_start_matches('v');

            semver::Version::parse(plain_version)
                // Discard the pre-release version, if any
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
#[derive(Clone, Debug, PartialEq, Eq)]
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cosmoshub() {
        let version_info = VersionInfo {
            name: "gaia".to_string(),
            app_name: "gaiad".to_string(),
            version: "v14.2.0".to_string(),
            git_commit: "3aa6e5058b4cbb4729300b239abfabd9a5b5691f".to_string(),
            build_tags: "netgo,ledger".to_string(),
            go_version: "go version go1.20.3 linux/amd64".to_string(),
            cosmos_sdk_version: "v0.45.16".to_string(),
            build_deps: vec![
                Module {
                    path: "github.com/cometbft/cometbft-db".to_string(),
                    version: "v0.7.0".to_string(),
                    sum: "h1:uBjbrBx4QzU0zOEnU8KxoDl18dMNgDh+zZRUE0ucsbo=".to_string(),
                },
                Module {
                    path: "github.com/confio/ics23/go".to_string(),
                    version: "v0.9.0".to_string(),
                    sum: "h1:cWs+wdbS2KRPZezoaaj+qBleXgUk5WOQFMP3CQFGTr4=".to_string(),
                },
                Module {
                    path: "github.com/cosmos/cosmos-db".to_string(),
                    version: "v0.0.0-20221226095112-f3c38ecb5e32".to_string(),
                    sum: "h1:zlCp9n3uwQieELltZWHRmwPmPaZ8+XoL2Sj+A2YJlr8=".to_string(),
                },
                Module {
                    path: "github.com/cosmos/cosmos-proto".to_string(),
                    version: "v1.0.0-beta.1".to_string(),
                    sum: "h1:iDL5qh++NoXxG8hSy93FdYJut4XfgbShIocllGaXx/0=".to_string(),
                },
                Module {
                    path: "github.com/cosmos/cosmos-sdk".to_string(),
                    version: "v0.45.16".to_string(),
                    sum: "".to_string(),
                },
                Module {
                    path: "github.com/cosmos/go-bip39".to_string(),
                    version: "v1.0.0".to_string(),
                    sum: "h1:pcomnQdrdH22njcAatO0yWojsUnCO3y2tNoV1cb6hHY=".to_string(),
                },
                Module {
                    path: "github.com/cosmos/iavl".to_string(),
                    version: "v0.19.5".to_string(),
                    sum: "h1:rGA3hOrgNxgRM5wYcSCxgQBap7fW82WZgY78V9po/iY=".to_string(),
                },
                Module {
                    path: "github.com/tendermint/tendermint".to_string(),
                    version: "v0.34.27".to_string(),
                    sum: "".to_string(),
                },
                Module {
                    path: "github.com/cosmos/ibc-go/v4".to_string(),
                    version: "v4.4.2".to_string(),
                    sum: "h1:PG4Yy0/bw6Hvmha3RZbc53KYzaCwuB07Ot4GLyzcBvo=".to_string(),
                },
                Module {
                    path: "github.com/cosmos/interchain-security/v2".to_string(),
                    version: "v2.0.0".to_string(),
                    sum: "".to_string(),
                },
            ],
        };

        let app_info = AppInfo::from(&version_info);

        assert_eq!(
            app_info,
            AppInfo {
                app_name: "gaiad".to_string(),
                version: "v14.2.0".to_string(),
                git_commit: "3aa6e5058b4cbb4729300b239abfabd9a5b5691f".to_string()
            }
        );

        let specs = Specs::try_from(version_info).unwrap();

        assert_eq!(
            specs,
            Specs {
                cosmos_sdk: Some(semver::Version::parse("0.45.16").unwrap()),
                ibc_go: Some(semver::Version::parse("4.4.2").unwrap()),
                consensus: Some(ConsensusVersion::Tendermint(
                    semver::Version::parse("0.34.27").unwrap()
                ))
            }
        );
    }

    #[test]
    fn phoenix() {
        let version_info = VersionInfo {
            name: "terra".to_string(),
            app_name: "terrad".to_string(),
            version: "20210603".to_string(),
            git_commit: "7cbb1f555b661a6ebec55231e563d2f94effc40e".to_string(),
            build_tags: "netgo,ledger".to_string(),
            go_version: "go version go1.20 linux/amd64".to_string(),
            cosmos_sdk_version: "v0.47.5".to_string(),
            build_deps: vec![
                Module {
                    path: "github.com/confio/ics23/go".to_string(),
                    version: "v0.9.0".to_string(),
                    sum: "h1:cWs+wdbS2KRPZezoaaj+qBleXgUk5WOQFMP3CQFGTr4=".to_string(),
                },
                Module {
                    path: "github.com/cometbft/cometbft-db".to_string(),
                    version: "v0.8.0".to_string(),
                    sum: "h1:vUMDaH3ApkX8m0KZvOFFy9b5DZHBAjsnEuo9AKVZpjo=".to_string(),
                },
                Module {
                    path: "github.com/cosmos/cosmos-proto".to_string(),
                    version: "v1.0.0-beta.3".to_string(),
                    sum: "h1:VitvZ1lPORTVxkmF2fAp3IiA61xVwArQYKXTdEcpW6o=".to_string(),
                },
                Module {
                    path: "github.com/cosmos/cosmos-sdk".to_string(),
                    version: "v0.47.5".to_string(),
                    sum: "".to_string(),
                },
                Module {
                    path: "github.com/cosmos/ibc-go/v7".to_string(),
                    version: "v7.3.0".to_string(),
                    sum: "".to_string(),
                },
                Module {
                    path: "github.com/cosmos/ics23/go".to_string(),
                    version: "v0.10.0".to_string(),
                    sum: "h1:iXqLLgp2Lp+EdpIuwXTYIQU+AiHj9mOC2X9ab++bZDM=".to_string(),
                },
                Module {
                    path: "github.com/cometbft/cometbft".to_string(),
                    version: "v0.37.2".to_string(),
                    sum: "h1:XB0yyHGT0lwmJlFmM4+rsRnczPlHoAKFX6K8Zgc2/Jc=".to_string(),
                },
            ],
        };

        let app_info = AppInfo::from(&version_info);

        assert_eq!(
            app_info,
            AppInfo {
                app_name: "terrad".to_string(),
                version: "20210603".to_string(),
                git_commit: "7cbb1f555b661a6ebec55231e563d2f94effc40e".to_string()
            }
        );

        let specs = Specs::try_from(version_info).unwrap();

        assert_eq!(
            specs,
            Specs {
                cosmos_sdk: Some(semver::Version::parse("0.47.5").unwrap()),
                ibc_go: Some(semver::Version::parse("7.3.0").unwrap()),
                consensus: Some(ConsensusVersion::Comet(
                    semver::Version::parse("0.37.2").unwrap()
                ))
            }
        );
    }
}
