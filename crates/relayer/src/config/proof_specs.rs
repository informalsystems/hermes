//! Custom `serde` deserializer for `ProofSpecs`

use core::fmt;
use ibc_relayer_types::core::ics23_commitment::specs::ProofSpecs;
use serde::{de, ser, Deserializer, Serializer};

pub fn serialize<S: Serializer>(
    proof_specs: &Option<ProofSpecs>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    match proof_specs {
        Some(proof_specs) => {
            let json_str = serde_json::to_string_pretty(proof_specs).map_err(ser::Error::custom)?;
            serializer.serialize_some(&json_str)
        }
        None => serializer.serialize_none(),
    }
}

struct ProofSpecsVisitor;

impl<'de> de::Visitor<'de> for ProofSpecsVisitor {
    type Value = Option<ProofSpecs>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("ICS23 proof-specs serialized as a JSON array")
    }

    fn visit_str<E: de::Error>(self, v: &str) -> Result<Self::Value, E> {
        serde_json::from_str(v).map(Some).map_err(E::custom)
    }

    fn visit_string<E: de::Error>(self, v: String) -> Result<Self::Value, E> {
        self.visit_str(&v)
    }
}

pub fn deserialize<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Option<ProofSpecs>, D::Error> {
    deserializer.deserialize_string(ProofSpecsVisitor)
}
