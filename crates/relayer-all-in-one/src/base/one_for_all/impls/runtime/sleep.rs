use core::time::Duration;

use async_trait::async_trait;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;

use crate::base::one_for_all::traits::runtime::OfaBaseRuntime;
use crate::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Runtime: OfaBaseRuntime> CanSleep for OfaRuntimeWrapper<Runtime> {
    async fn sleep(&self, duration: Duration) {
        self.runtime.sleep(duration).await
    }
}
