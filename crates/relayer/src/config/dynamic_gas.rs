use serde_derive::{Deserialize, Serialize};

flex_error::define_error! {
    Error {
        TooSmall
            { value: f64 }
            |e| {
                format_args!("`gas_multiplier` in dynamic_gas configuration must be greater than or equal to {}, found {}",
                DynamicGas::MIN_BOUND, e.value)
            },
    }
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, PartialOrd, Serialize)]
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
            gas_multiplier: DynamicGas,
        }

        let err = toml::from_str::<DummyConfig>("gas_multiplier = 0.9")
            .unwrap_err()
            .to_string();

        assert!(err.contains("expected a floating-point value less than"));
    }

    #[test]
    fn safe_gas_multiplier() {
        let gas_multiplier = DynamicGas::new(true, 0.6);
        assert!(
            gas_multiplier.is_err(),
            "Gas multiplier should be an error if value is lower than 1.0: {gas_multiplier:?}"
        );
    }

    #[test]
    fn unsafe_gas_multiplier() {
        let gas_multiplier = DynamicGas::unsafe_new(true, 0.6);
        assert_eq!(gas_multiplier.gas_price_multiplier, 0.6);
    }
}
