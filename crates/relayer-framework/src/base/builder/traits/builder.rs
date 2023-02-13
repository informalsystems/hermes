use async_trait::async_trait;

use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

#[async_trait]
pub trait TargetBuilder<Context, Target>: Async
where
    Target: Async,
    Context: HasErrorType,
{
    async fn build_target(context: &Context) -> Result<Target, Context::Error>;
}
