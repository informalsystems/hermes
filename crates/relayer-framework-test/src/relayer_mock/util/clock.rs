//! MockClock is a simple structure which allows multiple
//! entities to safely access a shared timestamp, represented by
//! a u128. The timestamp needs to be manually incremented.

use eyre::eyre;
use std::sync::{Arc, Mutex};

use crate::relayer_mock::{
    base::{error::Error, types::aliases::MockTimestamp},
    util::mutex::MutexUtil,
};

pub struct MockClock {
    timestamp: Arc<Mutex<MockTimestamp>>,
}

impl Default for MockClock {
    fn default() -> Self {
        Self {
            timestamp: Arc::new(Mutex::new(MockTimestamp(1))),
        }
    }
}

impl MockClock {
    pub fn increment_millis(&self, millis: u128) -> Result<(), Error> {
        let mut locked_timestamp = self.timestamp.acquire_mutex();
        *locked_timestamp = locked_timestamp
            .0
            .checked_add(millis)
            .ok_or_else(|| {
                Error::generic(eyre!(
                    "overflow when adding {} to {}",
                    locked_timestamp,
                    millis
                ))
            })?
            .into();

        Ok(())
    }

    pub fn get_timestamp(&self) -> MockTimestamp {
        let locked_timestamp = self.timestamp.acquire_mutex();

        (*locked_timestamp).clone()
    }
}
