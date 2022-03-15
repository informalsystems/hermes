/*!
   Utilities for suspending the test.
*/

use core::fmt::{Debug, Display};
use core::time::Duration;
use std::thread::sleep;
use tracing::{error, warn};

/**
   Call this function in the middle of a test code of interest,
   so that we can suspend the test and still interact with the
   spawned Gaia chains and chain supervisor for debugging.
*/
pub fn suspend<R>() -> R {
    warn!("suspending the test indefinitely. you can still interact with any spawned chains and relayers");

    loop {
        sleep(Duration::from_secs(999_999_999))
    }
}

pub fn hang_on_error<E: Debug + Display>(hang_on_fail: bool) -> impl FnOnce(E) -> E {
    move |e| {
        if hang_on_fail {
            error!("test failure occured with HANG_ON_FAIL=1, suspending the test to allow debugging: {:?}",
                e);

            suspend()
        } else {
            error!("test failure occured. set HANG_ON_FAIL=1 to suspend the test on failure for debugging: {}",
                e);
            e
        }
    }
}
