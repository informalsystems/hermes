use core::time::Duration;
use std::time::Instant;

use ibc_relayer_components::runtime::traits::time::HasTime;

use crate::types::runtime::TokioRuntimeContext;

impl HasTime for TokioRuntimeContext {
    type Time = Instant;

    fn now(&self) -> Instant {
        Instant::now()
    }

    fn duration_since(time: &Instant, other: &Instant) -> Duration {
        time.duration_since(*other)
    }
}
