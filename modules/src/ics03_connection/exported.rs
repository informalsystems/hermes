use super::error;
use anomaly::fail;
use serde_derive::{Deserialize, Serialize};

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

/// Function required by ICS 03. Returns the list of all possible versions that the connection
/// handshake protocol supports.
/// TODO: What are the precise values for the versions which this function returns? Perhaps encode the versions as constants.
pub fn get_compatible_versions() -> Vec<String> {
    let mut result = Vec::with_capacity(1);
    result[0] = String::from("test");

    result
}

/// Function required by ICS 03. Returns one version out of the supplied list of versions, which the
/// connection handshake protocol prefers.
/// TODO: Fix this with proper code.
pub fn pick_version(candidates: Vec<String>) -> Option<String> {
    let selection: String = candidates
        .get(0)
        .unwrap_or(&String::from("none"))
        .to_string();
    Some(selection)
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
