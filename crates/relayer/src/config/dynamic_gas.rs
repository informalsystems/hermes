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
                DynamicGas::MIN_BOUND, e.value)
            },

        MaxPriceTooSmall
            { value: f64 }
            |e| {
                format_args!("`max_gas_price` in dynamic_gas configuration must be greater than or equal to {}, found {}",
                DynamicGas::CHAIN_MIN_PRICE, e.value)
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
    const DEFAULT: f64 = 1.1;
    const DEFAULT_MAX_PRICE: f64 = 0.6;
    const MIN_BOUND: f64 = 1.0;
    // Using Osmosis min https://github.com/osmosis-labs/osmosis/blob/v21.2.1/x/txfees/keeper/mempool-1559/code.go#L45
    const CHAIN_MIN_PRICE: f64 = 0.0025;

    pub fn new(enabled: bool, multiplier: f64, max_price: f64) -> Result<Self, Error> {
        if multiplier < Self::MIN_BOUND {
            return Err(Error::multiplier_too_small(multiplier));
        }
        if max_price < Self::CHAIN_MIN_PRICE {
            return Err(Error::max_price_too_small(max_price));
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

    pub fn dynamic_gas_price(self) -> Option<f64> {
        if self.enabled {
            Some(self.gas_price_multiplier)
        } else {
            None
        }
    }
}

impl Default for DynamicGas {
    fn default() -> Self {
        Self {
            enabled: false,
            gas_price_multiplier: Self::DEFAULT,
            max_gas_price: Self::DEFAULT_MAX_PRICE,
        }
    }
}

impl<'de> Deserialize<'de> for DynamicGas {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value: serde_json::Value = Deserialize::deserialize(deserializer)?;

        let enabled = value["enabled"].as_bool().ok_or_else(|| {
            D::Error::invalid_value(Unexpected::Other("missing field"), &"enabled")
        })?;

        let gas_price_multiplier = value["gas_price_multiplier"].as_f64().ok_or_else(|| {
            D::Error::invalid_value(Unexpected::Other("missing field"), &"gas_price_multiplier")
        })?;

        let max_gas_price = value["max_gas_price"].as_f64().ok_or_else(|| {
            D::Error::invalid_value(Unexpected::Other("missing field"), &"gas_price_multiplier")
        })?;

        DynamicGas::new(enabled, gas_price_multiplier, max_gas_price).map_err(|e| {
            match e.detail() {
                ErrorDetail::MultiplierTooSmall(_) => D::Error::invalid_value(
                    Unexpected::Float(gas_price_multiplier),
                    &format!(
                        "a floating-point value less than {} for multiplier",
                        Self::MIN_BOUND
                    )
                    .as_str(),
                ),
                ErrorDetail::MaxPriceTooSmall(_) => D::Error::invalid_value(
                    Unexpected::Float(gas_price_multiplier),
                    &format!(
                        "a floating-point value less than {} for max gas price",
                        Self::CHAIN_MIN_PRICE
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
