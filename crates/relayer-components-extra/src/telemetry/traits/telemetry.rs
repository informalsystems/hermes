use ibc_relayer_components::core::traits::sync::Async;

pub trait HasTelemetry {
    type Telemetry: Async;

    fn telemetry(&self) -> &Self::Telemetry;
}
