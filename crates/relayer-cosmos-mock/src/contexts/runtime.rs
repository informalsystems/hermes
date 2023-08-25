use alloc::sync::Arc;
use core::time::Duration;
use ibc::core::timestamp::Timestamp;
use std::ops::Add;
use std::sync::Mutex;

use crate::types::error::Error;
use crate::util::mutex::MutexUtil;

pub struct MockRuntimeContext {
    pub clock: Arc<MockClock>,
}

impl MockRuntimeContext {
    pub fn new(clock: Arc<MockClock>) -> Self {
        Self { clock }
    }

    pub fn get_time(&self) -> Timestamp {
        self.clock.get_timestamp()
    }
}

impl Clone for MockRuntimeContext {
    fn clone(&self) -> Self {
        let clock = self.clock.clone();
        Self::new(clock)
    }
}

pub struct MockClock {
    timestamp: Arc<Mutex<Timestamp>>,
}

impl Default for MockClock {
    fn default() -> Self {
        Self {
            timestamp: Arc::new(Mutex::new(Timestamp::now())),
        }
    }
}

impl MockClock {
    pub fn increment_timestamp(&self, duration: Duration) -> Result<(), Error> {
        let mut locked_timestamp = self.timestamp.acquire_mutex();
        *locked_timestamp = locked_timestamp.add(duration).map_err(|_| {
            Error::invalid(format!(
                "overflow when adding {} to {:?}",
                locked_timestamp, duration
            ))
        })?;

        Ok(())
    }

    pub fn get_timestamp(&self) -> Timestamp {
        *self.timestamp.acquire_mutex()
    }
}
