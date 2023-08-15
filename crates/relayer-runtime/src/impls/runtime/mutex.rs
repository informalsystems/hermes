use async_trait::async_trait;
use futures::lock::{Mutex, MutexGuard};
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::runtime::traits::mutex::HasMutex;

use crate::types::runtime::TokioRuntimeContext;

#[async_trait]
impl HasMutex for TokioRuntimeContext {
    type Mutex<T: Async> = Mutex<T>;

    type MutexGuard<'a, T: Async> = MutexGuard<'a, T>;

    fn new_mutex<T: Async>(item: T) -> Self::Mutex<T> {
        Mutex::new(item)
    }

    async fn acquire_mutex<'a, T: Async>(mutex: &'a Self::Mutex<T>) -> Self::MutexGuard<'a, T> {
        mutex.lock().await
    }
}
