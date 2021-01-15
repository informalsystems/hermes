//! Capabilities: this is a placeholder.

#[derive(Clone, Debug, PartialEq)]
pub struct Capability {
    index: u64,
}

impl Capability {
    pub fn new() -> Capability {
        Self { index: 0x0 }
    }
}

impl Default for Capability {
    fn default() -> Self {
        Self::new()
    }
}
