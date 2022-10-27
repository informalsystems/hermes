use crate::base::core::traits::sync::Async;
use async_trait::async_trait;

use crate::std_prelude::*;

pub trait HasMutexGuard<'a>: Async {
    type MutexGuard: Send + Sync + 'a;
}

#[async_trait]
pub trait HasMutex: for<'a> HasMutexGuard<'a> {
    type Mutex: Async;

    async fn acquire_mutex<'a>(mutex: &'a Self::Mutex) -> <Self as HasMutexGuard<'a>>::MutexGuard;
}
