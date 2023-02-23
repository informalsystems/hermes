use core::fmt::Debug;
use core::ops::DerefMut;
use core::time::Duration;

use async_trait::async_trait;
use ibc_relayer_components::core::traits::sync::Async;

use crate::base::one_for_all::types::runtime::LogLevel;
use crate::std_prelude::*;

#[async_trait]
pub trait OfaBaseRuntime: Async {
    type Error: Async + Debug;

    type Time: Async;

    type Mutex<T: Async>: Async;

    type MutexGuard<'a, T: Async>: 'a + Send + Sync + DerefMut<Target = T>;

    async fn log(&self, level: LogLevel, message: &str);

    async fn sleep(&self, duration: Duration);

    fn now(&self) -> Self::Time;

    fn duration_since(time: &Self::Time, other: &Self::Time) -> Duration;

    fn new_mutex<T: Async>(item: T) -> Self::Mutex<T>;

    async fn acquire_mutex<'a, T: Async>(mutex: &'a Self::Mutex<T>) -> Self::MutexGuard<'a, T>;
}
