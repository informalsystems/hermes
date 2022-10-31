//! Configuration-related types.
//!
//! Implements defaults, as well as serializing and
//! deserializing with upper-bound verification.

pub use max_msg_num::MaxMsgNum;

pub mod max_msg_num {
    flex_error::define_error! {
        Error {
            TooSmall
                { value: usize }
                |e| {
                    format_args!("`max_msg_num` must be greater than or equal to {}, found {}",
                        MaxMsgNum::MIN_BOUND, e.value)
                },

            TooBig
                { value: usize }
                |e| {
                    format_args!("`max_msg_num` must be less than or equal to {}, found {}",
                        MaxMsgNum::MAX_BOUND, e.value)
                },
        }
    }

    #[derive(Debug, Clone, Copy)]
    pub struct MaxMsgNum(usize);

    impl MaxMsgNum {
        const DEFAULT: usize = 30;
        const MIN_BOUND: usize = 1;
        const MAX_BOUND: usize = 100;

        pub fn new(value: usize) -> Result<Self, Error> {
            if value < Self::MIN_BOUND {
                return Err(Error::too_small(value));
            }

            if value > Self::MAX_BOUND {
                return Err(Error::too_big(value));
            }

            Ok(Self(value))
        }

        pub fn to_usize(self) -> usize {
            self.0
        }
    }

    impl Default for MaxMsgNum {
        fn default() -> Self {
            Self(Self::DEFAULT)
        }
    }

    use serde::de::Unexpected;
    use serde::{de::Error as _, Deserialize, Deserializer, Serialize, Serializer};

    impl<'de> Deserialize<'de> for MaxMsgNum {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            let value = usize::deserialize(deserializer)?;

            MaxMsgNum::new(value).map_err(|e| match e.detail() {
                ErrorDetail::TooSmall(_) => D::Error::invalid_value(
                    Unexpected::Unsigned(value as u64),
                    &format!("a usize greater than or equal to {}", Self::MIN_BOUND).as_str(),
                ),
                ErrorDetail::TooBig(_) => D::Error::invalid_value(
                    Unexpected::Unsigned(value as u64),
                    &format!("a usize less than or equal to {}", Self::MAX_BOUND).as_str(),
                ),
            })
        }
    }

    impl Serialize for MaxMsgNum {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            self.0.serialize(serializer)
        }
    }

    impl From<MaxMsgNum> for usize {
        fn from(m: MaxMsgNum) -> Self {
            m.0
        }
    }
}

pub use max_tx_size::MaxTxSize;

pub mod max_tx_size {
    flex_error::define_error! {
        Error {
            TooBig
                { value: usize }
                |e| {
                    format_args!("`max_tx_size` must be less than or equal to {}, found {}",
                        MaxTxSize::MAX_BOUND, e.value)
                },
        }
    }

    #[derive(Debug, Clone, Copy)]
    pub struct MaxTxSize(usize);

    impl MaxTxSize {
        const DEFAULT: usize = 180000;
        const MAX_BOUND: usize = 8 * 1048576; // 8 MBytes

        pub fn new(value: usize) -> Result<Self, Error> {
            if value > Self::MAX_BOUND {
                return Err(Error::too_big(value));
            }

            Ok(Self(value))
        }

        pub fn max() -> Self {
            Self(Self::MAX_BOUND)
        }

        pub fn to_usize(self) -> usize {
            self.0
        }
    }

    impl Default for MaxTxSize {
        fn default() -> Self {
            Self(Self::DEFAULT)
        }
    }

    use serde::de::Unexpected;
    use serde::{de::Error as _, Deserialize, Deserializer, Serialize, Serializer};

    impl<'de> Deserialize<'de> for MaxTxSize {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            let value = usize::deserialize(deserializer)?;

            MaxTxSize::new(value).map_err(|e| match e.detail() {
                ErrorDetail::TooBig(_) => D::Error::invalid_value(
                    Unexpected::Unsigned(value as u64),
                    &format!("a usize less than or equal to {}", Self::MAX_BOUND).as_str(),
                ),
            })
        }
    }

    impl Serialize for MaxTxSize {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            self.0.serialize(serializer)
        }
    }

    impl From<MaxTxSize> for usize {
        fn from(m: MaxTxSize) -> Self {
            m.0
        }
    }
}

pub use memo::Memo;

pub mod memo {
    flex_error::define_error! {
        Error {
            TooLong
                { length: usize }
                |e| {
                    format_args!("`memo` must been no longer than {} characters, found length {}",
                        Memo::MAX_LEN, e.length)
                }
        }
    }

    /// A memo domain-type.
    ///
    /// Hermes uses this type to populate the `tx.memo` field for
    /// each transaction it submits.
    /// The memo can be configured on a per-chain basis.
    ///
    #[derive(Clone, Debug, Default)]
    pub struct Memo(String);

    impl Memo {
        const MAX_LEN: usize = 50;

        pub fn new(memo: impl Into<String>) -> Result<Self, Error> {
            let memo = memo.into();
            if memo.len() > Self::MAX_LEN {
                return Err(Error::too_long(memo.len()));
            }

            Ok(Self(memo))
        }

        pub fn apply_suffix(&mut self, suffix: &str) {
            // Add a separator if the memo
            // is pre-populated with some content already.
            if !self.0.is_empty() {
                self.0.push_str(" | ");
            }

            self.0.push_str(suffix);
        }

        pub fn as_str(&self) -> &str {
            &self.0
        }
    }

    use serde::{de::Error as _, Deserialize, Deserializer, Serialize, Serializer};

    impl<'de> Deserialize<'de> for Memo {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            let value = String::deserialize(deserializer)?;

            Memo::new(value).map_err(|e| match e.detail() {
                ErrorDetail::TooLong(sub) => D::Error::invalid_length(
                    sub.length,
                    &format!("a string length of at most {}", Self::MAX_LEN).as_str(),
                ),
            })
        }
    }

    impl Serialize for Memo {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            self.0.serialize(serializer)
        }
    }

    use core::fmt::{Display, Error as FmtError, Formatter};

    impl Display for Memo {
        fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
            write!(f, "{}", self.as_str())
        }
    }
}

#[cfg(test)]
#[allow(dead_code)] // the fields of the structs defined below are never accessed
mod tests {
    use super::*;

    use serde::Deserialize;
    use test_log::test;

    #[test]
    fn parse_invalid_max_msg_num_min() {
        #[derive(Debug, Deserialize)]
        struct DummyConfig {
            max_msg_num: MaxMsgNum,
        }

        let err = toml::from_str::<DummyConfig>("max_msg_num = 0")
            .unwrap_err()
            .to_string();

        assert!(err.contains("expected a usize greater than or equal to"));
    }

    #[test]
    fn parse_invalid_max_msg_num_max() {
        #[derive(Debug, Deserialize)]
        struct DummyConfig {
            max_msg_num: MaxMsgNum,
        }

        let err = toml::from_str::<DummyConfig>("max_msg_num = 1024")
            .unwrap_err()
            .to_string();

        assert!(err.contains("expected a usize less than or equal to"));
    }

    #[test]
    fn parse_invalid_max_tx_size() {
        #[derive(Debug, Deserialize)]
        struct DummyConfig {
            max_tx_size: MaxTxSize,
        }

        let err = toml::from_str::<DummyConfig>("max_tx_size = 9999999999")
            .unwrap_err()
            .to_string();

        assert!(err.contains("expected a usize less than or equal to"));
    }

    #[test]
    fn parse_invalid_memo() {
        #[derive(Debug, Deserialize)]
        struct DummyConfig {
            memo: Memo,
        }

        let err = toml::from_str::<DummyConfig>(
            r#"memo = "foo bar baz foo bar baz foo bar baz foo bar baz foo bar baz""#,
        )
        .unwrap_err()
        .to_string();

        assert!(err.contains("a string length of at most"));
    }
}
