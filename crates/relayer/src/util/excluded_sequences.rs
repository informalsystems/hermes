use serde::de::{Error, MapAccess, Visitor};
use serde::ser::SerializeMap;
use serde::Deserializer;
use serde::Serializer;
use serde_derive::Deserialize;
use serde_derive::Serialize;
use std::collections::BTreeMap;
use std::fmt;
use std::str::FromStr;

use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::ChannelId;

use crate::chain::cosmos::config::error::Error as ConfigError;

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct ExcludedSequences {
    #[serde(
        deserialize_with = "deserialize_excluded_sequences",
        serialize_with = "serialize_excluded_sequences",
        flatten
    )]
    pub map: BTreeMap<ChannelId, Vec<Sequence>>,
}

impl ExcludedSequences {
    pub fn new(map: BTreeMap<ChannelId, Vec<Sequence>>) -> Self {
        Self { map }
    }
}

fn serialize_excluded_sequences<S>(
    map: &BTreeMap<ChannelId, Vec<Sequence>>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let mut seq = serializer.serialize_map(Some(map.len()))?;
    for (k, v) in map {
        seq.serialize_entry(k, v)?;
    }
    seq.end()
}

fn deserialize_excluded_sequences<'de, D>(
    deserializer: D,
) -> Result<BTreeMap<ChannelId, Vec<Sequence>>, D::Error>
where
    D: Deserializer<'de>,
{
    deserializer.deserialize_map(ExcludedSequencesVisitor)
}

struct ExcludedSequencesVisitor;

impl<'de> Visitor<'de> for ExcludedSequencesVisitor {
    type Value = BTreeMap<ChannelId, Vec<Sequence>>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("expected list of excluded sequences")
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: MapAccess<'de>,
    {
        let mut map = BTreeMap::new();
        while let Some((key, value)) = access.next_entry::<String, toml::Value>()? {
            let channel_id = ChannelId::from_str(&key).map_err(|e| Error::custom(e.to_string()))?;
            let sequences =
                parse_sequence_range(&value).map_err(|e| Error::custom(e.to_string()))?;
            map.insert(channel_id, sequences);
        }
        Ok(map)
    }
}

fn parse_sequence_range(value: &toml::Value) -> Result<Vec<Sequence>, ConfigError> {
    let mut res = Vec::new();
    let sequences = value
        .as_array()
        .ok_or_else(ConfigError::expected_excluded_sequences_array)?;
    for sequence in sequences.iter() {
        if let Some(seq_str) = sequence.as_str() {
            let (start, end) = get_start_and_end(seq_str)?;
            for i in start..=end {
                let seq = Sequence::from(i);
                res.push(seq);
            }
        } else if let Some(seq) = sequence.as_integer() {
            let seq = Sequence::from(seq as u64);
            res.push(seq);
        }
    }
    Ok(res)
}

fn get_start_and_end(value: &str) -> Result<(u64, u64), ConfigError> {
    let split: Vec<&str> = value.split('-').collect();
    let start: u64 = split
        .first()
        .ok_or_else(|| ConfigError::missing_start_excluded_sequence(value.to_string()))?
        .parse()
        .map_err(|e| ConfigError::parsing_start_excluded_sequence_failed(value.to_string(), e))?;
    let end: u64 = split
        .last()
        .ok_or_else(|| ConfigError::missing_end_excluded_sequence(value.to_string()))?
        .parse()
        .map_err(|e| ConfigError::parsing_end_excluded_sequence_failed(value.to_string(), e))?;

    Ok((start, end))
}
