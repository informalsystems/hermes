use async_trait::async_trait;
use core::future::Future;
use core::time::Duration;

use crate::one_for_all::traits::error::OfaErrorContext;
use crate::one_for_all::traits::runtime::{OfaRuntime, OfaRuntimeContext};
use crate::std_prelude::*;
use crate::traits::contexts::error::HasError;
use crate::traits::runtime::sleep::CanSleep;
use crate::traits::runtime::spawn::{HasSpawner, Spawner};
use crate::traits::runtime::time::{HasTime, Time};

pub struct OfaTime<Runtime: OfaRuntime> {
    pub time: Runtime::Time,
}

impl<Runtime: OfaRuntime> HasError for OfaRuntimeContext<Runtime> {
    type Error = OfaErrorContext<Runtime::Error>;
}

#[async_trait]
impl<Runtime: OfaRuntime> CanSleep for OfaRuntimeContext<Runtime> {
    async fn sleep(&self, duration: Duration) {
        self.runtime.sleep(duration).await
    }
}

impl<Runtime: OfaRuntime> HasSpawner for OfaRuntimeContext<Runtime> {
    type Spawner = Self;

    fn spawner(&self) -> Self::Spawner {
        self.clone()
    }
}

impl<Runtime: OfaRuntime> Spawner for OfaRuntimeContext<Runtime> {
    fn spawn<F>(&self, task: F)
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        self.runtime.spawn(task)
    }
}

impl<Runtime: OfaRuntime> HasTime for OfaRuntimeContext<Runtime> {
    type Time = OfaTime<Runtime>;

    fn now(&self) -> Self::Time {
        let time = self.runtime.now();
        OfaTime { time }
    }
}

impl<Runtime: OfaRuntime> Time for OfaTime<Runtime> {
    fn duration_since(&self, other: &Self) -> Duration {
        Runtime::duration_since(&self.time, &other.time)
    }
}
