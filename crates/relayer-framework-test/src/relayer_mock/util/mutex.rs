//! MutexUtil is a helper trait to simplify the error handling
//! when locking a Mutex.

use std::sync::{Arc, Mutex, MutexGuard};

pub trait MutexUtil<T> {
    fn acquire_mutex(&self) -> MutexGuard<T>;
}

impl<T> MutexUtil<T> for Arc<Mutex<T>> {
    fn acquire_mutex(&self) -> MutexGuard<T> {
        match self.lock() {
            Ok(locked_mutex) => locked_mutex,
            Err(e) => panic!("poisoned mutex: {}", e),
        }
    }
}
