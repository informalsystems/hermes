use std::convert::TryFrom;

use ibc_proto::ibc::core::connection::v1::Version as RawVersion;
use tendermint_proto::DomainType;

use crate::ics03_connection::error::{Error, Kind};
use std::str::FromStr;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Version {
    /// unique version identifier
    identifier: String,
    /// list of features compatible with the specified identifier
    features: Vec<String>,
}

impl DomainType<RawVersion> for Version {}

impl TryFrom<RawVersion> for Version {
    type Error = anomaly::Error<Kind>;
    fn try_from(value: RawVersion) -> Result<Self, Self::Error> {
        Ok(Version {
            identifier: value.identifier,
            features: value.features,
        })
    }
}

impl From<Version> for RawVersion {
    fn from(value: Version) -> Self {
        Self {
            identifier: value.identifier,
            features: value.features,
        }
    }
}

impl Default for Version {
    fn default() -> Self {
        Version {
            identifier: "1".to_string(),
            features: vec!["ORDER_ORDERED".to_string(), "ORDER_UNORDERED".to_string()],
        }
    }
}

impl FromStr for Version {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Version::decode(s.as_bytes()).map_err(|e| Kind::InvalidVersion.context(e))?)
    }
}

impl std::fmt::Display for Version {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            String::from_utf8(Version::encode_vec(&self).unwrap()).unwrap()
        )
    }
}

pub fn default_version_string() -> String {
    Version::default().to_string()
}

pub fn get_compatible_versions() -> Vec<String> {
    vec![default_version_string()]
}

pub fn pick_version(
    supported_versions: Vec<String>,
    counterparty_versions: Vec<String>,
) -> Result<String, Error> {
    let mut intersection: Vec<Version> = vec![];
    for s in supported_versions.iter() {
        let supported_version =
            Version::decode(s.as_bytes()).map_err(|e| Kind::InvalidVersion.context(e))?;
        for c in counterparty_versions.iter() {
            let counterparty_version = Version::from_str(c.as_str())?;
            if supported_version.identifier != counterparty_version.identifier {
                continue;
            }
            // TODO - perform feature intersection and error if empty
            intersection.append(&mut vec![supported_version.clone()]);
        }
    }
    intersection.sort_by(|a, b| a.identifier.cmp(&b.identifier));
    if intersection.is_empty() {
        return Err(Kind::NoCommonVersion.into());
    }
    Ok(intersection[0].to_string())
}

pub fn validate_versions(versions: Vec<String>) -> Result<Vec<String>, Error> {
    if versions.is_empty() {
        return Err(Kind::InvalidVersion
            .context("no versions".to_string())
            .into());
    }
    for version_str in versions.iter() {
        validate_version(version_str.clone())?;
    }
    Ok(versions)
}

pub fn validate_version(raw_version: String) -> Result<String, Error> {
    let version =
        Version::from_str(raw_version.as_ref()).map_err(|e| Kind::InvalidVersion.context(e))?;

    if version.identifier.trim().is_empty() {
        return Err(Kind::InvalidVersion
            .context("empty version string".to_string())
            .into());
    }
    for feature in version.features {
        if feature.trim().is_empty() {
            return Err(Kind::InvalidVersion
                .context("empty feature string".to_string())
                .into());
        }
    }
    Ok(raw_version)
}

#[cfg(test)]
mod tests {
    use crate::ics03_connection::version::{
        default_version_string, get_compatible_versions, pick_version, validate_versions, Version,
    };
    use std::str::FromStr;

    fn good_versions() -> Vec<String> {
        vec![
            Version::default(),
            Version {
                identifier: "2".to_string(),
                features: vec!["ORDER_RANDOM".to_string(), "ORDER_UNORDERED".to_string()],
            },
        ]
        .into_iter()
        .map(|v| v.to_string())
        .collect()
    }

    fn bad_versions_identifier() -> Vec<String> {
        vec![Version {
            identifier: "".to_string(),
            features: vec!["ORDER_RANDOM".to_string(), "ORDER_UNORDERED".to_string()],
        }]
        .into_iter()
        .map(|v| v.to_string())
        .collect()
    }

    fn bad_versions_features() -> Vec<String> {
        vec![Version {
            identifier: "2".to_string(),
            features: vec!["".to_string()],
        }]
        .into_iter()
        .map(|v| v.to_string())
        .collect()
    }

    fn overlapping() -> (Vec<String>, Vec<String>, String) {
        (
            vec![
                Version::default(),
                Version {
                    identifier: "3".to_string(),
                    features: vec![],
                },
                Version {
                    identifier: "4".to_string(),
                    features: vec![],
                },
            ]
            .into_iter()
            .map(|v| v.to_string())
            .collect(),
            vec![
                Version {
                    identifier: "2".to_string(),
                    features: vec![],
                },
                Version {
                    identifier: "4".to_string(),
                    features: vec![],
                },
                Version {
                    identifier: "3".to_string(),
                    features: vec![],
                },
            ]
            .into_iter()
            .map(|v| v.to_string())
            .collect(),
            // Should pick version 3 as it's the lowest of the intersection {3, 4}
            Version {
                identifier: "3".to_string(),
                features: vec![],
            }
            .to_string(),
        )
    }

    fn disjoint() -> (Vec<String>, Vec<String>, String) {
        (
            vec![Version {
                identifier: "1".to_string(),
                features: vec![],
            }]
            .into_iter()
            .map(|v| v.to_string())
            .collect(),
            vec![Version {
                identifier: "2".to_string(),
                features: vec![],
            }]
            .into_iter()
            .map(|v| v.to_string())
            .collect(),
            "".to_string(),
        )
    }

    #[test]
    fn verify() {
        struct Test {
            name: String,
            versions: Vec<String>,
            want_pass: bool,
        }
        let tests: Vec<Test> = vec![
            Test {
                name: "Compatible versions".to_string(),
                versions: get_compatible_versions(),
                want_pass: true,
            },
            Test {
                name: "Multiple versions".to_string(),
                versions: good_versions(),
                want_pass: true,
            },
            Test {
                name: "Bad version identifier".to_string(),
                versions: bad_versions_identifier(),
                want_pass: false,
            },
            Test {
                name: "Bad version feature".to_string(),
                versions: bad_versions_features(),
                want_pass: false,
            },
            Test {
                name: "Bad versions empty".to_string(),
                versions: vec![],
                want_pass: false,
            },
        ];

        for test in tests {
            let versions = validate_versions(test.versions);

            assert_eq!(
                test.want_pass,
                versions.is_ok(),
                "Validate versions failed for test {} with error {:?}",
                test.name,
                versions.err(),
            );
        }
    }
    #[test]
    fn pick() {
        struct Test {
            name: String,
            supported: Vec<String>,
            counterparty: Vec<String>,
            picked: String,
            want_pass: bool,
        }
        let tests: Vec<Test> = vec![
            Test {
                name: "Compatible versions".to_string(),
                supported: get_compatible_versions(),
                counterparty: get_compatible_versions(),
                picked: default_version_string(),
                want_pass: true,
            },
            Test {
                name: "Overlapping versions".to_string(),
                supported: overlapping().0,
                counterparty: overlapping().1,
                picked: overlapping().2,
                want_pass: true,
            },
            Test {
                name: "Disjoint versions".to_string(),
                supported: disjoint().0,
                counterparty: disjoint().1,
                picked: disjoint().2,
                want_pass: false,
            },
        ];

        for test in tests {
            let version = pick_version(test.supported, test.counterparty);

            assert_eq!(
                test.want_pass,
                version.is_ok(),
                "Validate versions failed for test {}",
                test.name,
            );

            if test.want_pass {
                assert_eq!(version.unwrap(), test.picked);
            }
        }
    }
    #[test]
    fn serialize() {
        let def = Version::default();
        let def_raw = def.to_string();
        let def_back = Version::from_str(def_raw.as_ref()).unwrap();
        assert_eq!(def, def_back);
    }
}
