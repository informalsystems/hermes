use async_trait::async_trait;
use core::time::Duration;

use crate::base::one_for_all::traits::runtime::OfaRuntime;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::base::runtime::traits::sleep::CanSleep;
use crate::std_prelude::*;

#[async_trait]
impl<Runtime: OfaRuntime> CanSleep for OfaRuntimeWrapper<Runtime> {
    async fn sleep(&self, duration: Duration) {
        self.runtime.sleep(duration).await
    }
}
