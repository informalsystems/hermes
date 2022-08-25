use async_trait::async_trait;
use core::future::Future;
use core::time::Duration;

use crate::core::traits::core::Async;
use crate::one_for_all::traits::error::OfaError;
use crate::std_prelude::*;

#[derive(Clone)]
pub struct OfaRuntimeContext<Runtime> {
    pub runtime: Runtime,
}

impl<Runtime> OfaRuntimeContext<Runtime> {
    pub fn new(runtime: Runtime) -> Self {
        Self { runtime }
    }
}

pub enum LogLevel {
    Error,
    Warn,
    Info,
    Debug,
    Trace,
}

#[async_trait]
pub trait OfaRuntime: Clone + Async {
    type Error: OfaError;

    type Time: Async;

    async fn log(&self, level: LogLevel, message: &str);

    async fn sleep(&self, duration: Duration);

    fn now(&self) -> Self::Time;

    fn duration_since(time: &Self::Time, other: &Self::Time) -> Duration;

    fn spawn<F>(&self, task: F)
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static;
}
