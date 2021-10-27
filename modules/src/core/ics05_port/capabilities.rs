//! Capabilities: this is a placeholder.

#[derive(Clone, Debug, PartialEq)]
pub struct Capability {
    index: u64,
}

impl Capability {
    pub fn new() -> Capability {
        Self { index: 0x0 }
    }

    pub fn index(&self) -> u64 {
        self.index
    }
}

impl Default for Capability {
    fn default() -> Self {
        Self::new()
    }
}

impl From<u64> for Capability {
    fn from(index: u64) -> Self {
        Self { index }
    }
}
