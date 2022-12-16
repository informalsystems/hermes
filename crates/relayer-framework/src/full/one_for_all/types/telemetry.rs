use alloc::sync::Arc;

pub struct OfaTelemetryWrapper<Telemetry> {
    pub telemetry: Arc<Telemetry>,
}

impl<Telemetry> OfaTelemetryWrapper<Telemetry> {
    pub fn new(telemetry: Telemetry) -> Self {
        Self {
            telemetry: Arc::new(telemetry),
        }
    }
}

impl<Telemetry> Clone for OfaTelemetryWrapper<Telemetry> {
    fn clone(&self) -> Self {
        Self {
            telemetry: self.telemetry.clone(),
        }
    }
}
