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
            timestamp: Arc::new(Mutex::new(1)),
        }
    }
}

impl MockClock {
    pub fn increment_millis(&self, millis: u128) -> Result<(), Error> {
        let mut locked_timestamp = self.timestamp.acquire_mutex()?;
        *locked_timestamp = locked_timestamp.checked_add(millis).ok_or_else(|| {
            Error::generic(eyre!(
                "overflow when adding {} to {}",
                locked_timestamp,
                millis
            ))
        })?;

        Ok(())
    }

    pub fn increment_seconds(&self, seconds: u128) -> Result<(), Error> {
        let mut locked_timestamp = self.timestamp.acquire_mutex()?;
        *locked_timestamp = locked_timestamp
            .checked_add(seconds * 1000)
            .ok_or_else(|| {
                Error::generic(eyre!(
                    "overflow when adding {} to {}",
                    locked_timestamp,
                    seconds * 1000
                ))
            })?;

        Ok(())
    }

    pub fn get_timestamp(&self) -> Result<MockTimestamp, Error> {
        let locked_timestamp = self.timestamp.acquire_mutex()?;

        Ok(*locked_timestamp)
    }
}
