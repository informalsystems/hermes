/*!
   Utilities for suspending the test.
*/

use core::time::Duration;
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::thread::sleep;
use tracing::{error, warn};

use crate::error::Error;

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

/**
   Suspends the test using [`suspend`] if `hang_on_fail` is `true` and if
   the continuation returns `Err`.

   The parameter `hang_on_fail` should be obtained from
   [`TestConfig`](crate::types::config::TestConfig),
   which in turns is set from the `HANG_ON_FAIL` environment variable.
*/
pub fn hang_on_error<R>(
    hang_on_fail: bool,
    cont: impl FnOnce() -> Result<R, Error>,
) -> Result<R, Error> {
    let result = catch_unwind(AssertUnwindSafe(cont));

    match result {
        Err(e) => {
            if hang_on_fail {
                let message = e.downcast::<&str>().ok();
                error!("test panicked with HANG_ON_FAIL=1, suspending the test to allow debugging: {:?}",
                    message);

                suspend()
            } else {
                error!("test panicked. set HANG_ON_FAIL=1 to suspend the test on failure for debugging.");

                resume_unwind(e)
            }
        }
        Ok(Err(e)) => {
            if hang_on_fail {
                error!("test failure occured with HANG_ON_FAIL=1, suspending the test to allow debugging: {:?}",
                    e);

                suspend()
            } else {
                error!("test failure occured. set HANG_ON_FAIL=1 to suspend the test on failure for debugging: {:?}",
                    e);

                Err(e)
            }
        }
        Ok(Ok(res)) => Ok(res),
    }
}
