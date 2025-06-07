use core::fmt;
use serde::de::Error as DeserializeError;
use serde::de::Unexpected;
use serde::Deserialize;
use serde::Deserializer;
use serde_derive::Serialize;

flex_error::define_error! {
    Error {
        MultiplierTooSmall
            { value: f64 }
            |e| {
                format_args!("`multiplier` in dynamic_gas configuration must be greater than or equal to {}, found {}",
                DynamicGasPrice::MIN_MULTIPLIER, e.value)
            },
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DynamicGasType {
    SkipFeeMarket,
    Osmosis,
    CosmosEvm,
}

impl fmt::Display for DynamicGasType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DynamicGasType::SkipFeeMarket => write!(f, "SkipFeeMarket"),
            DynamicGasType::Osmosis => write!(f, "Osmosis"),
            DynamicGasType::CosmosEvm => write!(f, "CosmosEVM"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Serialize)]
pub struct DynamicGasPrice {
    pub enabled: bool,
    pub multiplier: f64,
    pub max: f64,
    pub r#type: Option<DynamicGasType>,
}

impl DynamicGasPrice {
    const DEFAULT_MULTIPLIER: f64 = 1.1;
    const DEFAULT_MAX: f64 = 0.6;
    const MIN_MULTIPLIER: f64 = 1.0;

    pub fn enabled(
        multiplier: f64,
        max: f64,
        r#type: Option<DynamicGasType>,
    ) -> Result<Self, Error> {
        Self::new(true, multiplier, max, r#type)
    }

    pub fn disabled() -> Self {
        Self {
            enabled: false,
            multiplier: Self::DEFAULT_MULTIPLIER,
            max: Self::DEFAULT_MAX,
            r#type: None,
        }
    }

    pub fn new(
        enabled: bool,
        multiplier: f64,
        max: f64,
        r#type: Option<DynamicGasType>,
    ) -> Result<Self, Error> {
        if multiplier < Self::MIN_MULTIPLIER {
            return Err(Error::multiplier_too_small(multiplier));
        }

        Ok(Self {
            enabled,
            multiplier,
            max,
            r#type,
        })
    }

    // Unsafe GasMultiplier used for test cases only.
    pub fn unsafe_new(
        enabled: bool,
        multiplier: f64,
        max: f64,
        r#type: Option<DynamicGasType>,
    ) -> Self {
        Self {
            enabled,
            multiplier,
            max,
            r#type,
        }
    }
}

impl Default for DynamicGasPrice {
    fn default() -> Self {
        Self::disabled()
    }
}

impl<'de> Deserialize<'de> for DynamicGasPrice {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct DynGas {
            enabled: bool,
            multiplier: f64,
            max: f64,
            r#type: Option<DynamicGasType>,
        }

        let DynGas {
            enabled,
            multiplier,
            max,
            r#type,
        } = DynGas::deserialize(deserializer)?;

        DynamicGasPrice::new(enabled, multiplier, max, r#type).map_err(|e| match e.detail() {
            ErrorDetail::MultiplierTooSmall(_) => D::Error::invalid_value(
                Unexpected::Float(multiplier),
                &format!(
                    "a floating-point value greater than {}",
                    Self::MIN_MULTIPLIER
                )
                .as_str(),
            ),
        })
    }
}

#[cfg(test)]
#[allow(dead_code)] // the field of the struct `DummyConfig` defined below is never accessed
mod tests {
    use super::*;

    use serde::Deserialize;
    use test_log::test;

    #[test]
    fn parse_invalid_gas_multiplier() {
        #[derive(Debug, Deserialize)]
        struct DummyConfig {
            dynamic_gas: DynamicGasPrice,
        }

        let err = toml::from_str::<DummyConfig>(
            "dynamic_gas = { enabled = true, multiplier = 0.9, max = 0.6 }",
        )
        .unwrap_err()
        .to_string();

        println!("err: {err}");

        assert!(err.contains("expected a floating-point value greater than"));
    }

    #[test]
    fn safe_gas_multiplier() {
        let dynamic_gas = DynamicGasPrice::new(true, 0.6, 0.6, None);
        assert!(
            dynamic_gas.is_err(),
            "Gas multiplier should be an error if value is lower than 1.0: {dynamic_gas:?}"
        );
    }

    #[test]
    fn unsafe_gas_multiplier() {
        let dynamic_gas = DynamicGasPrice::unsafe_new(true, 0.6, 0.4, None);
        assert_eq!(dynamic_gas.multiplier, 0.6);
        assert_eq!(dynamic_gas.max, 0.4);
    }

    #[test]
    fn parse_valid_dynamic_gas_type() {
        #[derive(Debug, Deserialize)]
        struct DummyConfig {
            dynamic_gas: DynamicGasPrice,
        }
        let config: DummyConfig = toml::from_str(
            "dynamic_gas = { enabled = true, multiplier = 1.1, max = 0.6, type = 'skip_fee_market' }",
        )
        .unwrap();

        assert_eq!(config.dynamic_gas.multiplier, 1.1);
        assert_eq!(config.dynamic_gas.max, 0.6);
        assert_eq!(
            config.dynamic_gas.r#type,
            Some(DynamicGasType::SkipFeeMarket)
        );
    }

    #[test]
    fn parse_invalid_dynamic_gas_type() {
        #[derive(Debug, Deserialize)]
        struct DummyConfig {
            dynamic_gas: DynamicGasPrice,
        }
        let err = toml::from_str::<DummyConfig>(
            "dynamic_gas = { enabled = true, multiplier = 1.1, max = 0.6, type = 'invalid_type' }",
        )
        .unwrap_err()
        .to_string();

        assert!(err.contains("unknown variant `invalid_type`, expected one of `skip_fee_market`, `osmosis`, `cosmos_evm`"));
    }

    #[test]
    fn parse_no_dynamic_gas_type() {
        #[derive(Debug, Deserialize)]
        struct DummyConfig {
            dynamic_gas: DynamicGasPrice,
        }
        let config: DummyConfig =
            toml::from_str("dynamic_gas = { enabled = true, multiplier = 1.1, max = 0.6 }")
                .unwrap();

        assert_eq!(config.dynamic_gas.multiplier, 1.1);
        assert_eq!(config.dynamic_gas.max, 0.6);
        assert!(config.dynamic_gas.r#type.is_none());
    }
}
