/*!
   Utilities for retrying test operations.
*/

use core::time::Duration;
use eyre::eyre;
use std::thread::sleep;
use tracing::trace;

use crate::error::Error;

/**
   A simplified version of retry logic used for testing.
   We do not need complicated retry logic as we need this
   only to test eventual consistency which should reach
   within a few seconds.
*/
pub fn assert_eventually_succeed<R>(
    task_name: &str,
    attempts: u16,
    interval: Duration,
    task: impl Fn() -> Result<R, Error>,
) -> Result<R, Error> {
    sleep(interval);
    for _ in 0..attempts {
        match task() {
            Ok(res) => return Ok(res),
            Err(e) => {
                trace!("retrying task that failed with error: {}", e);
                sleep(interval)
            }
        }
    }

    Err(Error::generic(eyre!(
        "Expected task to eventually succeeed, but failed after {} attempts: {}",
        attempts,
        task_name
    )))
}
