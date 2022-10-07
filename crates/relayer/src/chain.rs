pub mod client;
pub mod cosmos;
pub mod counterparty;
pub mod endpoint;
pub mod handle;
pub mod requests;
pub mod runtime;
pub mod tracking;

use serde::{de::Error, Deserialize, Serialize};

// NOTE(new): When adding a variant to `ChainType`, make sure to update
//            the `Deserialize` implementation below and the tests.
//            See the NOTE(new) comments below.

#[derive(Copy, Clone, Debug, Serialize)]
/// Types of chains the relayer can relay to and from
pub enum ChainType {
    /// Chains based on the Cosmos SDK
    CosmosSdk,
}

impl<'de> Deserialize<'de> for ChainType {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let original = String::deserialize(deserializer)?;
        let s = original.to_ascii_lowercase().replace('-', "");

        match s.as_str() {
            "cosmossdk" => Ok(Self::CosmosSdk),

            // NOTE(new): Add a case here
            _ => Err(D::Error::unknown_variant(&original, &["cosmos-sdk"])), // NOTE(new): mention the new variant here
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Copy, Clone, Debug, Serialize, Deserialize)]
    pub struct Config {
        tpe: ChainType,
    }

    fn parse(variant: &str) -> Result<ChainType, toml::de::Error> {
        toml::from_str::<Config>(&format!("tpe = '{variant}'")).map(|e| e.tpe)
    }

    #[test]
    fn deserialize() {
        use ChainType::*;

        assert!(matches!(parse("CosmosSdk"), Ok(CosmosSdk)));
        assert!(matches!(parse("cosmossdk"), Ok(CosmosSdk)));
        assert!(matches!(parse("cosmos-sdk"), Ok(CosmosSdk)));

        // NOTE(new): Add tests here

        assert!(matches!(parse("hello-world"), Err(_)));
    }
}
