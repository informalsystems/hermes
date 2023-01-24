use async_trait::async_trait;
use core::ops::DerefMut;

use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

#[async_trait]
pub trait HasMutex: Async {
    type Mutex<T: Async>: Async;

    type MutexGuard<'a, T: Async>: 'a + Send + Sync + DerefMut<Target = T>;

    fn new_mutex<T: Async>(item: T) -> Self::Mutex<T>;

    async fn acquire_mutex<'a, T: Async>(mutex: &'a Self::Mutex<T>) -> Self::MutexGuard<'a, T>;
}
