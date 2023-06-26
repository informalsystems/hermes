use core::time::Duration;

use async_trait::async_trait;
use ibc_relayer_components::runtime::traits::sleep::CanSleep;

use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::one_for_all::types::runtime::OfaRuntimeWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Runtime> CanSleep for OfaRuntimeWrapper<Runtime>
where
    Runtime: OfaRuntime,
{
    async fn sleep(&self, duration: Duration) {
        self.runtime.sleep(duration).await
    }
}
