use serde::de::Unexpected;
use serde::{de::Error as _, Deserialize, Deserializer, Serialize, Serializer};

flex_error::define_error! {
    Error {
        TooSmall
            { value: f64 }
            |e| {
                format_args!("`gas_multiplier` must be greater than or equal to {}, found {}",
                    GasMultiplier::MIN_BOUND, e.value)
            },
    }
}

#[derive(Debug, Clone, Copy)]
pub struct GasMultiplier(f64);

impl GasMultiplier {
    const DEFAULT: f64 = 1.1;
    const MIN_BOUND: f64 = 1.0;

    pub fn new(value: f64) -> Result<Self, Error> {
        if value < Self::MIN_BOUND {
            return Err(Error::too_small(value));
        }
        Ok(Self(value))
    }

    // Unsafe GasMultiplier used for test cases only.
    pub fn unsafe_new(value: f64) -> Self {
        Self(value)
    }

    pub fn to_f64(self) -> f64 {
        self.0
    }
}

impl Default for GasMultiplier {
    fn default() -> Self {
        Self(Self::DEFAULT)
    }
}

impl<'de> Deserialize<'de> for GasMultiplier {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value = f64::deserialize(deserializer)?;

        GasMultiplier::new(value).map_err(|e| match e.detail() {
            ErrorDetail::TooSmall(_) => D::Error::invalid_value(
                Unexpected::Float(value),
                &format!("a floating-point value less than {}", Self::MIN_BOUND).as_str(),
            ),
        })
    }
}

impl Serialize for GasMultiplier {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl From<GasMultiplier> for f64 {
    fn from(m: GasMultiplier) -> Self {
        m.0
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
            gas_multiplier: GasMultiplier,
        }

        let err = toml::from_str::<DummyConfig>("gas_multiplier = 0.9")
            .unwrap_err()
            .to_string();

        assert!(err.contains("expected a floating-point value less than"));
    }

    #[test]
    fn safe_gas_multiplier() {
        let gas_multiplier = GasMultiplier::new(0.6);
        assert!(
            gas_multiplier.is_err(),
            "Gas multiplier should be an error if value is lower than 1.0: {gas_multiplier:?}"
        );
    }

    #[test]
    fn unsafe_gas_multiplier() {
        let gas_multiplier = GasMultiplier::unsafe_new(0.6);
        assert_eq!(gas_multiplier.to_f64(), 0.6);
    }
}
