use async_trait::async_trait;
use core::time::Duration;

use crate::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::base::runtime::traits::sleep::CanSleep;
use crate::std_prelude::*;

#[async_trait]
impl<Runtime: OfaBaseRuntime> CanSleep for OfaRuntimeWrapper<Runtime> {
    async fn sleep(&self, duration: Duration) {
        self.runtime.sleep(duration).await
    }
}
