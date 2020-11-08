use std::convert::TryFrom;

use ibc_proto::ibc::core::connection::v1::Version as RawVersion;
use tendermint_proto::DomainType;

use crate::ics03_connection::error::{Error, Kind};

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

pub fn default_version_string() -> String {
    String::from_utf8(Version::encode_vec(&Version::default()).unwrap()).unwrap()
}

pub fn get_compatible_versions() -> Vec<String> {
    vec![default_version_string()]
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
        Version::decode(raw_version.as_bytes()).map_err(|e| Kind::InvalidVersion.context(e))?;

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
    use crate::ics03_connection::version::Version;
    use tendermint_proto::DomainType;

    #[test]
    fn default_test() {
        let def = Version::default();
        assert_ne!(def.identifier.len(), 0);
    }

    #[test]
    fn serialize() {
        let def = Version::default();
        let mut wire = vec![];
        def.encode(&mut wire).unwrap();

        let str_wire = std::str::from_utf8(&wire).unwrap().to_string();

        let u8_wire = str_wire.as_bytes().to_vec();
        assert_eq!(wire, u8_wire);

        let def_back = Version::decode(wire.as_ref()).unwrap();
        assert_eq!(def, def_back);
    }
}
