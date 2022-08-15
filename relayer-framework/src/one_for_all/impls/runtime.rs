use async_trait::async_trait;
use core::time::Duration;

use crate::one_for_all::traits::error::OfaErrorContext;
use crate::one_for_all::traits::runtime::{OfaRuntime, OfaRuntimeContext};
use crate::std_prelude::*;
use crate::traits::contexts::error::HasError;
use crate::traits::runtime::sleep::CanSleep;

impl<Runtime: OfaRuntime> HasError for OfaRuntimeContext<Runtime> {
    type Error = OfaErrorContext<Runtime::Error>;
}

#[async_trait]
impl<Runtime: OfaRuntime> CanSleep for OfaRuntimeContext<Runtime> {
    async fn sleep(&self, duration: Duration) {
        self.runtime.sleep(duration).await
    }
}
