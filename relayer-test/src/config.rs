use core::fmt::{Debug, Display};
use std::path::PathBuf;
use tracing::error;

use crate::util::hang::hang;

pub struct TestConfig {
    pub chain_command_path: String,
    pub chain_store_dir: PathBuf,
    pub hang_on_fail: bool,
}

impl TestConfig {
    pub fn hang_on_error<E: Debug + Display>(&self) -> impl FnOnce(E) -> E {
        let hang_on_fail = self.hang_on_fail;
        move |e| {
            if hang_on_fail {
                error!("test failure occured with HANG_ON_FAIL=1, hanging the test to allow debugging: {:?}",
                    e);

                hang();
            } else {
                error!("test failure occured. set HANG_ON_FAIL=1 to hang the test on failure for debugging: {}",
                    e);
            }

            e
        }
    }
}
