//! MutexUtil is a helper trait to simplify the error handling
//! when locking a Mutex.

use std::sync::{Arc, Mutex, MutexGuard};

use ibc_relayer_components::core::traits::sync::Async;

pub trait MutexUtil<T: Async> {
    fn acquire_mutex(&self) -> MutexGuard<T>;
}

impl<T: Async> MutexUtil<T> for Arc<Mutex<T>> {
    fn acquire_mutex(&self) -> MutexGuard<T> {
        match self.lock() {
            Ok(locked_mutex) => locked_mutex,
            Err(e) => {
                panic!("poisoned mutex: {e}")
            }
        }
    }
}
