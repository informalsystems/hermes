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
                format_args!("`gas_price_multiplier` in dynamic_gas configuration must be greater than or equal to {}, found {}",
                DynamicGas::MIN_MULTIPLIER, e.value)
            },
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Serialize)]
pub struct DynamicGas {
    pub enabled: bool,
    pub gas_price_multiplier: f64,
    pub max_gas_price: f64,
}

impl DynamicGas {
    const DEFAULT_MULTIPLIER: f64 = 1.1;
    const DEFAULT_MAX_PRICE: f64 = 0.6;
    const MIN_MULTIPLIER: f64 = 1.0;

    pub fn new(enabled: bool, multiplier: f64, max_price: f64) -> Result<Self, Error> {
        if multiplier < Self::MIN_MULTIPLIER {
            return Err(Error::multiplier_too_small(multiplier));
        }

        Ok(Self {
            enabled,
            gas_price_multiplier: multiplier,
            max_gas_price: max_price,
        })
    }

    // Unsafe GasMultiplier used for test cases only.
    pub fn unsafe_new(enabled: bool, multiplier: f64, max_price: f64) -> Self {
        Self {
            enabled,
            gas_price_multiplier: multiplier,
            max_gas_price: max_price,
        }
    }
}

impl Default for DynamicGas {
    fn default() -> Self {
        Self {
            enabled: false,
            gas_price_multiplier: Self::DEFAULT_MULTIPLIER,
            max_gas_price: Self::DEFAULT_MAX_PRICE,
        }
    }
}

impl<'de> Deserialize<'de> for DynamicGas {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct DynGas {
            enabled: bool,
            gas_price_multiplier: f64,
            max_gas_price: f64,
        }

        let DynGas {
            enabled,
            gas_price_multiplier,
            max_gas_price,
        } = DynGas::deserialize(deserializer)?;

        DynamicGas::new(enabled, gas_price_multiplier, max_gas_price).map_err(|e| {
            match e.detail() {
                ErrorDetail::MultiplierTooSmall(_) => D::Error::invalid_value(
                    Unexpected::Float(gas_price_multiplier),
                    &format!(
                        "a floating-point value less than {} for multiplier",
                        Self::MIN_MULTIPLIER
                    )
                    .as_str(),
                ),
            }
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
            dynamic_gas: DynamicGas,
        }

        let err = toml::from_str::<DummyConfig>(
            "dynamic_gas = { enabled = true, gas_price_multiplier = 0.9, max_gas_price = 0.6 }",
        )
        .unwrap_err()
        .to_string();

        println!("err: {err}");

        assert!(err.contains("expected a floating-point value less than"));
    }

    #[test]
    fn safe_gas_multiplier() {
        let dynamic_gas = DynamicGas::new(true, 0.6, 0.6);
        assert!(
            dynamic_gas.is_err(),
            "Gas multiplier should be an error if value is lower than 1.0: {dynamic_gas:?}"
        );
    }

    #[test]
    fn unsafe_gas_multiplier() {
        let dynamic_gas = DynamicGas::unsafe_new(true, 0.6, 0.4);
        assert_eq!(dynamic_gas.gas_price_multiplier, 0.6);
        assert_eq!(dynamic_gas.max_gas_price, 0.4);
    }
}
