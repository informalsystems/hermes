//! MockClock is a simple structure which allows multiple
//! entities to safely access a shared timestamp, represented by
//! a u128. The timestamp needs to be manually incremented.

use eyre::eyre;
use std::sync::{Arc, Mutex};

use crate::relayer_mock::base::error::{BaseError, Error};
use crate::relayer_mock::base::types::aliases::MockTimestamp;
use crate::relayer_mock::util::mutex::MutexUtil;

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
    pub fn increment_timestamp(&self, duration: MockTimestamp) -> Result<(), Error> {
        let mut locked_timestamp = self.timestamp.acquire_mutex();
        *locked_timestamp = locked_timestamp
            .0
            .checked_add(duration.0)
            .ok_or_else(|| {
                BaseError::generic(eyre!(
                    "overflow when adding {} to {}",
                    locked_timestamp,
                    duration,
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
