use serde::de::Error as DeserializeError;
use serde::de::Unexpected;
use serde::Deserialize;
use serde::Deserializer;
use serde_derive::Serialize;

flex_error::define_error! {
    Error {
        TooSmall
            { value: f64 }
            |e| {
                format_args!("`gas_price_multiplier` in dynamic_gas configuration must be greater than or equal to {}, found {}",
                DynamicGas::MIN_BOUND, e.value)
            },
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Serialize)]
pub struct DynamicGas {
    pub enabled: bool,
    pub gas_price_multiplier: f64,
}

impl DynamicGas {
    const DEFAULT: f64 = 1.1;
    const MIN_BOUND: f64 = 1.0;

    pub fn new(enabled: bool, value: f64) -> Result<Self, Error> {
        if value < Self::MIN_BOUND {
            return Err(Error::too_small(value));
        }
        Ok(Self {
            enabled,
            gas_price_multiplier: value,
        })
    }

    // Unsafe GasMultiplier used for test cases only.
    pub fn unsafe_new(enabled: bool, value: f64) -> Self {
        Self {
            enabled,
            gas_price_multiplier: value,
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

        DynamicGas::new(enabled, gas_price_multiplier).map_err(|e| match e.detail() {
            ErrorDetail::TooSmall(_) => D::Error::invalid_value(
                Unexpected::Float(gas_price_multiplier),
                &format!("a floating-point value less than {}", Self::MIN_BOUND).as_str(),
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
            dynamic_gas: DynamicGas,
        }

        let err = toml::from_str::<DummyConfig>(
            "dynamic_gas = { enabled = true, gas_price_multiplier = 0.9 }",
        )
        .unwrap_err()
        .to_string();

        println!("err: {err}");

        assert!(err.contains("expected a floating-point value less than"));
    }

    #[test]
    fn safe_gas_multiplier() {
        let dynamic_gas = DynamicGas::new(true, 0.6);
        assert!(
            dynamic_gas.is_err(),
            "Gas multiplier should be an error if value is lower than 1.0: {dynamic_gas:?}"
        );
    }

    #[test]
    fn unsafe_gas_multiplier() {
        let dynamic_gas = DynamicGas::unsafe_new(true, 0.6);
        assert_eq!(dynamic_gas.gas_price_multiplier, 0.6);
    }
}