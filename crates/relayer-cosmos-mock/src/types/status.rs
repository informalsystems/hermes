use ibc::core::timestamp::Timestamp;
use ibc::Height;

#[derive(Clone, Debug)]
pub struct ChainStatus {
    pub timestamp: Timestamp,
    pub height: Height,
}

impl ChainStatus {
    pub fn new(height: Height, timestamp: Timestamp) -> Self {
        Self { height, timestamp }
    }
}

impl From<(Height, Timestamp)> for ChainStatus {
    fn from(s: (Height, Timestamp)) -> Self {
        ChainStatus {
            height: s.0,
            timestamp: s.1,
        }
    }
}
