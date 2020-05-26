use super::error;
use crate::ics24_host::identifier::ConnectionId;
use anomaly::fail;
use serde_derive::{Deserialize, Serialize};

pub trait Channel {
    type ValidationError: std::error::Error;
    fn state(&self) -> &State;
    fn ordering(&self) -> &Order;
    fn counterparty(&self) -> Box<dyn ChannelCounterparty<ValidationError = super::error::Error>>;
    fn connection_hops(&self) -> Vec<ConnectionId>;
    fn version(&self) -> String;
    fn validate_basic(&self) -> Result<(), Self::ValidationError>;
}

pub trait ChannelCounterparty {
    type ValidationError: std::error::Error;
    fn port_id(&self) -> String;
    fn channel_id(&self) -> String;
    fn validate_basic(&self) -> Result<(), Self::ValidationError>;
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum State {
    Uninitialized = 0,
    Init,
    TryOpen,
    Open,
    Closed,
}

impl State {
    /// Yields the state as a string
    pub fn as_string(&self) -> &'static str {
        match self {
            Self::Uninitialized => "UNINITIALIZED",
            Self::Init => "INIT",
            Self::TryOpen => "TRYOPEN",
            Self::Open => "OPEN",
            Self::Closed => "CLOSED",
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
            "CLOSED" => Ok(Self::Closed),
            _ => fail!(error::Kind::UnknownState, s),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Order {
    None = 0,
    Unordered,
    Ordered,
}

impl Order {
    /// Yields the Order as a string
    pub fn as_string(&self) -> &'static str {
        match self {
            Self::None => "UNINITIALIZED",
            Self::Unordered => "UNORDERED",
            Self::Ordered => "ORDERED",
        }
    }
}

impl std::str::FromStr for Order {
    type Err = error::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "UNINITIALIZED" => Ok(Self::None),
            "UNORDERED" => Ok(Self::Unordered),
            "ORDERED" => Ok(Self::Ordered),
            _ => fail!(error::Kind::UnknownOrderType, s),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    #[test]
    fn parse_channel_ordering_type() {
        use super::Order;

        struct Test {
            ordering: &'static str,
            want_res: Order,
            want_err: bool,
        }
        let tests: Vec<Test> = vec![
            Test {
                ordering: "UNINITIALIZED",
                want_res: Order::None,
                want_err: false,
            },
            Test {
                ordering: "UNORDERED",
                want_res: Order::Unordered,
                want_err: false,
            },
            Test {
                ordering: "ORDERED",
                want_res: Order::Ordered,
                want_err: false,
            },
            Test {
                ordering: "UNKNOWN_ORDER",
                want_res: Order::None,
                want_err: true,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            match Order::from_str(test.ordering) {
                Ok(res) => {
                    assert!(!test.want_err);
                    assert_eq!(test.want_res, res);
                }
                Err(_) => assert!(test.want_err, "parse failed"),
            }
        }
    }

    #[test]
    fn parse_channel_state() {
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
                state: "CLOSED",
                want_res: State::Closed,
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
