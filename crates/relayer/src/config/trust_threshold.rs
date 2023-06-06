use std::{fmt, marker::PhantomData};

use serde::{
    de::{self, MapAccess, Visitor},
    Deserialize, Deserializer, Serialize, Serializer,
};

use tendermint_light_client::verifier::types::TrustThreshold;

pub fn serialize<S: Serializer>(
    trust_threshold: &TrustThreshold,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    TrustThreshold::serialize(trust_threshold, serializer)
}

pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<TrustThreshold, D::Error> {
    deserializer.deserialize_any(StringOrStruct(PhantomData))
}

// This is a Visitor that forwards string types to T's `FromStr` impl and
// forwards map types to T's `Deserialize` impl. The `PhantomData` is to
// keep the compiler from complaining about T being an unused generic type
// parameter. We need T in order to know the Value type for the Visitor
// impl.
struct StringOrStruct<T>(PhantomData<fn() -> T>);

impl<'de> Visitor<'de> for StringOrStruct<TrustThreshold> {
    type Value = TrustThreshold;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("string (eg. '1/3') or { numerator = <int>, denominator = <int> }")
    }

    fn visit_str<E>(self, value: &str) -> Result<TrustThreshold, E>
    where
        E: de::Error,
    {
        let parts: Vec<&str> = value.split('/').collect();

        if parts.len() != 2 {
            return Err(serde::de::Error::custom(format!(
                "invalid trust threshold, must be a fraction: {value}",
            )));
        }

        let (num, denom) = (parts[0].parse(), parts[1].parse());

        match (num, denom) {
            (Ok(num), Ok(denom)) => TrustThreshold::new(num, denom).map_err(|e| {
                serde::de::Error::custom(format!(
                    "invalid trust threshold, must be a fraction: {e}"
                ))
            }),

            _ => Err(serde::de::Error::custom(format!(
                "invalid trust threshold, must be a fraction: {value}",
            ))),
        }
    }

    fn visit_map<M>(self, map: M) -> Result<TrustThreshold, M::Error>
    where
        M: MapAccess<'de>,
    {
        // `MapAccessDeserializer` is a wrapper that turns a `MapAccess`
        // into a `Deserializer`, allowing it to be used as the input to T's
        // `Deserialize` implementation. T then deserializes itself using
        // the entries from the map visitor.
        TrustThreshold::deserialize(de::value::MapAccessDeserializer::new(map))
    }
}
