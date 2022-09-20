use core::fmt::{Display, Error as FmtError, Formatter};

/// REST server configuration
#[derive(Clone, Debug)]
pub struct Config {
    pub host: String,
    pub port: u16,
}

impl Config {
    pub fn new(host: String, port: u16) -> Self {
        Self { host, port }
    }

    pub fn address(&self) -> (&str, u16) {
        (&self.host, self.port)
    }
}

impl Display for Config {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "{}:{}", self.host, self.port)
    }
}
