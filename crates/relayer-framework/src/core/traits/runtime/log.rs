use async_trait::async_trait;

use crate::core::traits::core::Async;
use crate::std_prelude::*;

pub struct LevelError;

pub struct LevelWarn;

pub struct LevelInfo;

pub struct LevelDebug;

pub struct LevelTrace;

#[async_trait]
pub trait HasLogger<Level>: Async {
    async fn log(&self, level: Level, message: &str);
}

pub trait HasBasicLogger:
    HasLogger<LevelError>
    + HasLogger<LevelWarn>
    + HasLogger<LevelInfo>
    + HasLogger<LevelDebug>
    + HasLogger<LevelTrace>
{
}

impl<Context> HasBasicLogger for Context where
    Context: HasLogger<LevelError>
        + HasLogger<LevelWarn>
        + HasLogger<LevelInfo>
        + HasLogger<LevelDebug>
        + HasLogger<LevelTrace>
{
}
