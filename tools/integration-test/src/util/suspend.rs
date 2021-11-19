/*!
   Utilities for suspending the test.
*/

use core::time::Duration;
use std::thread::sleep;
use tracing::warn;

/**
   Call this function in the middle of a test code of interest,
   so that we can suspend the test and still interact with the
   spawned Gaia chains and chain supervisor for debugging.
*/
pub fn suspend() -> ! {
    warn!("suspending the test indefinitely. you can still interact with any spawned chains and relayers");

    loop {
        sleep(Duration::from_secs(999_999_999))
    }
}
