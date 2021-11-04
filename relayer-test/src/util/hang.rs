use core::time::Duration;
use std::thread::sleep;
use tracing::warn;

/// Call this function in the middle of a test code of interest,
/// so that we can hang the test and still interact with the
/// spawned Gaia chains and chain supervisor for debugging.
pub fn hang() -> ! {
    warn!("hanging the test indefinitely. you can still interact with any spawned chains and relayers");

    loop {
        sleep(Duration::from_secs(999_999_999))
    }
}
