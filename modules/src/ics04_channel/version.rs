use std::convert::TryFrom;

use ibc_proto::ibc::core::connection::v1::Version as RawVersion;
use tendermint_proto::Protobuf;

use crate::ics04_channel::error;
use crate::primitives::{String, ToString};
use std::prelude::*;
use std::str::FromStr;
use std::vec::Vec;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Version {
    /// unique version identifier
    identifier: String,
    /// list of features compatible with the specified identifier
    features: Vec<String>,
}

impl Protobuf<RawVersion> for Version {}

impl TryFrom<RawVersion> for Version {
    type Error = error::Error;
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
            features: vec!["TOKEN_TRANSFER".to_string()],
        }
    }
}

impl FromStr for Version {
    type Err = error::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Version::decode(s.as_bytes()).map_err(error::invalid_version_error)
    }
}

impl std::fmt::Display for Version {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            String::from_utf8(Version::encode_vec(self).unwrap()).unwrap()
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
) -> Result<String, error::Error> {
    let mut intersection: Vec<Version> = vec![];
    for s in supported_versions.iter() {
        let supported_version =
            Version::decode(s.as_bytes()).map_err(error::invalid_version_error)?;
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
        return Err(error::no_common_version_error());
    }
    Ok(intersection[0].to_string())
}

pub fn validate_versions(versions: Vec<String>) -> Result<Vec<String>, error::Error> {
    if versions.is_empty() {
        return Err(error::empty_version_error());
    }
    for version_str in versions.iter() {
        validate_version(version_str.clone())?;
    }
    Ok(versions)
}

pub fn validate_version(raw_version: String) -> Result<String, error::Error> {
    let version = Version::from_str(raw_version.as_ref())?;

    if version.identifier.trim().is_empty() {
        return Err(error::empty_version_error());
    }
    for feature in version.features {
        if feature.trim().is_empty() {
            return Err(error::empty_version_error());
        }
    }
    Ok(raw_version)
}
