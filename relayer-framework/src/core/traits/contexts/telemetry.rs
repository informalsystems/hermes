use crate::core::traits::core::Async;

pub trait HasTelemetry {
    const TELEMETRY_ENABLED: bool;

    type Telemetry: Async;

    fn telemetry(&self) -> &Self::Telemetry;
}
