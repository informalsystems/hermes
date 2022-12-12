//! MutexUtil is a helper trait to simplify the error handling
//! when locking a Mutex.

use std::sync::{Arc, Mutex, MutexGuard};

use crate::relayer_mock::base::error::Error;

pub trait MutexUtil<T> {
    fn acquire_mutex(&self) -> Result<MutexGuard<T>, Error>;
}

impl<T> MutexUtil<T> for Arc<Mutex<T>> {
    fn acquire_mutex(&self) -> Result<MutexGuard<T>, Error> {
        match self.lock() {
            Ok(locked_mutex) => Ok(locked_mutex),
            Err(_) => Err(Error::poisoned_mutex()),
        }
    }
}
