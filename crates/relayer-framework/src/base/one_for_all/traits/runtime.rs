use async_trait::async_trait;
use core::fmt::Debug;
use core::future::Future;
use core::time::Duration;

use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

#[derive(Clone)]
pub struct OfaRuntimeWrapper<Runtime> {
    pub runtime: Runtime,
}

impl<Runtime> OfaRuntimeWrapper<Runtime> {
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
    type Error: Async + Debug;

    type Time: Async;

    type Sender<T>: Async
    where
        T: Async;

    type Receiver<T>: Async
    where
        T: Async;

    type SenderOnce<T>: Async
    where
        T: Async;

    type ReceiverOnce<T>: Async
    where
        T: Async;

    async fn log(&self, level: LogLevel, message: &str);

    async fn sleep(&self, duration: Duration);

    fn now(&self) -> Self::Time;

    fn duration_since(time: &Self::Time, other: &Self::Time) -> Duration;

    fn spawn<F>(&self, task: F)
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static;

    fn new_channel<T>() -> (Self::Sender<T>, Self::Receiver<T>)
    where
        T: Async;

    fn send<T>(sender: &Self::Sender<T>, value: T) -> Result<(), Self::Error>
    where
        T: Async;

    async fn receive<T>(receiver: &Self::Receiver<T>) -> Result<T, Self::Error>
    where
        T: Async;

    async fn try_receive<T>(receiver: &Self::Receiver<T>) -> Result<Option<T>, Self::Error>
    where
        T: Async;

    fn new_channel_once<T>() -> (Self::SenderOnce<T>, Self::ReceiverOnce<T>)
    where
        T: Async;

    fn send_once<T>(sender: Self::SenderOnce<T>, value: T) -> Result<(), Self::Error>
    where
        T: Async;

    async fn receive_once<T>(receiver: Self::ReceiverOnce<T>) -> Result<T, Self::Error>
    where
        T: Async;
}
