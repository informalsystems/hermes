use std::str::FromStr;

use serde::{Deserialize, Deserializer, Serialize, Serializer};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct RefreshRate {
    numerator: u64,
    denominator: u64,
}

impl RefreshRate {
    pub fn new(numerator: u64, denominator: u64) -> Self {
        Self {
            numerator,
            denominator,
        }
    }

    pub fn as_f64(self) -> f64 {
        self.numerator as f64 / self.denominator as f64
    }
}

impl FromStr for RefreshRate {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parts: Vec<&str> = s.split('/').collect();

        if parts.len() != 2 {
            return Err(format!("invalid refresh rate, must be a fraction: {s}"));
        }

        let (num, denom) = (parts[0].parse(), parts[1].parse());

        if let (Ok(num), Ok(denom)) = (num, denom) {
            Ok(RefreshRate::new(num, denom))
        } else {
            Err(format!("invalid refresh rate, must be a fraction: {s}",))
        }
    }
}

impl Serialize for RefreshRate {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&format!("{}/{}", self.numerator, self.denominator))
    }
}

impl<'de> Deserialize<'de> for RefreshRate {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = String::deserialize(deserializer)?;
        RefreshRate::from_str(&s).map_err(serde::de::Error::custom)
    }
}
