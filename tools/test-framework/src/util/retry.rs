/*!
   Utilities for retrying test operations.
*/

use core::time::Duration;
use std::thread::sleep;
use tracing::{debug, info};

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
    for i in 0..attempts {
        match task() {
            Ok(res) => {
                info!("task {} succeed after {} tries", task_name, i);
                return Ok(res);
            }
            Err(e) => {
                debug!("retrying task {} that failed with error: {}", task_name, e);
                sleep(interval)
            }
        }
    }

    Err(Error::retry(task_name.to_string(), attempts))
}
