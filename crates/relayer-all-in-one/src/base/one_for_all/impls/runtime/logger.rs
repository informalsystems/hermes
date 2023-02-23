use async_trait::async_trait;
use ibc_relayer_components::runtime::traits::log::{
    HasLogger, LevelDebug, LevelError, LevelInfo, LevelTrace, LevelWarn,
};

use crate::base::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::base::one_for_all::types::runtime::{LogLevel, OfaRuntimeWrapper};
use crate::std_prelude::*;

#[async_trait]
impl<Runtime: OfaBaseRuntime> HasLogger<LevelError> for OfaRuntimeWrapper<Runtime> {
    async fn log(&self, _level: LevelError, message: &str) {
        self.runtime.log(LogLevel::Error, message).await;
    }
}

#[async_trait]
impl<Runtime: OfaBaseRuntime> HasLogger<LevelWarn> for OfaRuntimeWrapper<Runtime> {
    async fn log(&self, _level: LevelWarn, message: &str) {
        self.runtime.log(LogLevel::Warn, message).await;
    }
}

#[async_trait]
impl<Runtime: OfaBaseRuntime> HasLogger<LevelInfo> for OfaRuntimeWrapper<Runtime> {
    async fn log(&self, _level: LevelInfo, message: &str) {
        self.runtime.log(LogLevel::Info, message).await;
    }
}

#[async_trait]
impl<Runtime: OfaBaseRuntime> HasLogger<LevelDebug> for OfaRuntimeWrapper<Runtime> {
    async fn log(&self, _level: LevelDebug, message: &str) {
        self.runtime.log(LogLevel::Debug, message).await;
    }
}

#[async_trait]
impl<Runtime: OfaBaseRuntime> HasLogger<LevelTrace> for OfaRuntimeWrapper<Runtime> {
    async fn log(&self, _level: LevelTrace, message: &str) {
        self.runtime.log(LogLevel::Trace, message).await;
    }
}
