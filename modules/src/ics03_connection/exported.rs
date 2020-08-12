use super::error;
use crate::ics23_commitment::CommitmentPrefix;
use anomaly::fail;
use serde_derive::{Deserialize, Serialize};

pub trait Connection {
    type ValidationError: std::error::Error;

    fn state(&self) -> &State;
    fn client_id(&self) -> String;
    fn counterparty(
        &self,
    ) -> Box<dyn ConnectionCounterparty<ValidationError = super::error::Error>>;
    fn versions(&self) -> Vec<String>;
    fn validate_basic(&self) -> Result<(), Self::ValidationError>;
}

pub trait ConnectionCounterparty {
    type ValidationError: std::error::Error;

    fn client_id(&self) -> String;
    fn connection_id(&self) -> String;
    fn prefix(&self) -> &CommitmentPrefix;
    fn validate_basic(&self) -> Result<(), Self::ValidationError>;
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum State {
    Uninitialized = 0,
    Init,
    TryOpen,
    Open,
}

impl State {
    /// Yields the State as a string.
    pub fn as_string(&self) -> &'static str {
        match self {
            Self::Uninitialized => "UNINITIALIZED",
            Self::Init => "INIT",
            Self::TryOpen => "TRYOPEN",
            Self::Open => "OPEN",
        }
    }

    /// Parses the State from a i32.
    pub fn from_i32(nr: i32) -> Self {
        match nr {
            1 => Self::Init,
            2 => Self::TryOpen,
            3 => Self::Open,
            _ => Self::Uninitialized,
        }
    }
}

impl std::str::FromStr for State {
    type Err = error::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "UNINITIALIZED" => Ok(Self::Uninitialized),
            "INIT" => Ok(Self::Init),
            "TRYOPEN" => Ok(Self::TryOpen),
            "OPEN" => Ok(Self::Open),
            _ => fail!(error::Kind::UnknownState, s),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    #[test]
    fn parse_connection_state() {
        use super::State;

        struct Test {
            state: &'static str,
            want_res: State,
            want_err: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                state: "UNINITIALIZED",
                want_res: State::Uninitialized,
                want_err: false,
            },
            Test {
                state: "INIT",
                want_res: State::Init,
                want_err: false,
            },
            Test {
                state: "TRYOPEN",
                want_res: State::TryOpen,
                want_err: false,
            },
            Test {
                state: "OPEN",
                want_res: State::Open,
                want_err: false,
            },
            Test {
                state: "INVALID_STATE",
                want_res: State::Open,
                want_err: true,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            match State::from_str(test.state) {
                Ok(res) => {
                    assert!(!test.want_err);
                    assert_eq!(test.want_res, res);
                }
                Err(_) => assert!(test.want_err, "parse failed"),
            }
        }
    }
}
