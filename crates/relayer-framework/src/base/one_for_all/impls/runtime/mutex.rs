use async_trait::async_trait;

use crate::base::core::traits::sync::Async;
use crate::base::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::base::runtime::traits::mutex::HasMutex;
use crate::std_prelude::*;

#[async_trait]
impl<Runtime> HasMutex for OfaRuntimeWrapper<Runtime>
where
    Runtime: OfaBaseRuntime,
{
    type Mutex<T: Async> = Runtime::Mutex<T>;

    type MutexGuard<'a, T: Async> = Runtime::MutexGuard<'a, T>;

    fn new_mutex<T: Async>(item: T) -> Self::Mutex<T> {
        Runtime::new_mutex(item)
    }

    async fn acquire_mutex<'a, T: Async>(mutex: &'a Self::Mutex<T>) -> Self::MutexGuard<'a, T> {
        Runtime::acquire_mutex(mutex).await
    }
}
