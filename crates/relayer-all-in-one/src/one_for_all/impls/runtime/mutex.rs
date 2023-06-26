use async_trait::async_trait;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::runtime::traits::mutex::HasMutex;

use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Runtime> HasMutex for OfaRuntimeWrapper<Runtime>
where
    Runtime: OfaRuntime,
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
