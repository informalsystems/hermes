use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};

pub type RwArc<T> = Arc<RwLock<T>>;

/**
   Utility methods for acquiring an `Arc<RwLock<T>>` lock without having
   to assert the success acquire every time.

   The current code base panics if the lock acquire fails due to
   [poisoned lock](https://doc.rust-lang.org/std/sync/struct.PoisonError.html),
   as the error is non-recoverable anyway.

   Using the `LockExt` methods, we can avoid having to write `.unwrap()`
   or `.expect("poisoned lock")` everywhere in the code base.
*/
pub trait LockExt<T> {
    fn new_lock(val: T) -> Self;

    fn acquire_read(&self) -> RwLockReadGuard<'_, T>;

    fn acquire_write(&self) -> RwLockWriteGuard<'_, T>;
}

impl<T> LockExt<T> for Arc<RwLock<T>> {
    fn new_lock(val: T) -> Self {
        Arc::new(RwLock::new(val))
    }

    fn acquire_read(&self) -> RwLockReadGuard<'_, T> {
        self.read().expect("poisoned lock")
    }

    fn acquire_write(&self) -> RwLockWriteGuard<'_, T> {
        self.write().expect("poisoned lock")
    }
}
