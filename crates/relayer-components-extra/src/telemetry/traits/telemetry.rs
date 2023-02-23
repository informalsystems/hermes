use crate::base::core::traits::sync::Async;

pub trait HasTelemetry {
    type Telemetry: Async;

    fn telemetry(&self) -> &Self::Telemetry;
}
