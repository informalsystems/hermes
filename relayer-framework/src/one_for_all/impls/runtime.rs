use async_trait::async_trait;
use core::time::Duration;

use crate::one_for_all::impls::error::OfaErrorContext;
use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::std_prelude::*;
use crate::traits::contexts::error::HasError;
use crate::traits::runtime::sleep::CanSleep;

pub struct OfaRuntimeContext<Runtime> {
    pub runtime: Runtime,
}

impl<Runtime> OfaRuntimeContext<Runtime> {
    pub fn new(runtime: Runtime) -> Self {
        Self { runtime }
    }
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
