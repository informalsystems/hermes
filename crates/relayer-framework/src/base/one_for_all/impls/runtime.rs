use async_trait::async_trait;
use core::future::Future;
use core::time::Duration;

use crate::base::core::traits::error::HasError;
use crate::base::core::traits::runtime::log::{
    HasLogger, LevelDebug, LevelError, LevelInfo, LevelTrace, LevelWarn,
};
use crate::base::core::traits::runtime::sleep::CanSleep;
use crate::base::core::traits::runtime::spawn::{HasSpawner, Spawner};
use crate::base::core::traits::runtime::time::{HasTime, Time};
use crate::base::one_for_all::traits::error::OfaErrorContext;
use crate::base::one_for_all::traits::runtime::{LogLevel, OfaRuntime, OfaRuntimeContext};
use crate::std_prelude::*;

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

#[async_trait]
impl<Runtime: OfaRuntime> HasLogger<LevelError> for OfaRuntimeContext<Runtime> {
    async fn log(&self, _level: LevelError, message: &str) {
        self.runtime.log(LogLevel::Error, message).await;
    }
}

#[async_trait]
impl<Runtime: OfaRuntime> HasLogger<LevelWarn> for OfaRuntimeContext<Runtime> {
    async fn log(&self, _level: LevelWarn, message: &str) {
        self.runtime.log(LogLevel::Warn, message).await;
    }
}

#[async_trait]
impl<Runtime: OfaRuntime> HasLogger<LevelInfo> for OfaRuntimeContext<Runtime> {
    async fn log(&self, _level: LevelInfo, message: &str) {
        self.runtime.log(LogLevel::Info, message).await;
    }
}

#[async_trait]
impl<Runtime: OfaRuntime> HasLogger<LevelDebug> for OfaRuntimeContext<Runtime> {
    async fn log(&self, _level: LevelDebug, message: &str) {
        self.runtime.log(LogLevel::Debug, message).await;
    }
}

#[async_trait]
impl<Runtime: OfaRuntime> HasLogger<LevelTrace> for OfaRuntimeContext<Runtime> {
    async fn log(&self, _level: LevelTrace, message: &str) {
        self.runtime.log(LogLevel::Trace, message).await;
    }
}
