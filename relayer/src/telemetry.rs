// If the `telemetry` feature is enabled, re-export the `ibc-telemetry` state.
#[cfg(feature = "telemetry")]
pub type Telemetry = std::sync::Arc<ibc_telemetry::TelemetryState>;

// Otherwise, define and export a dummy type.
#[cfg(not(feature = "telemetry"))]
#[derive(Clone, Debug)]
pub struct TelemetryDisabled;

#[cfg(not(feature = "telemetry"))]
pub type Telemetry = TelemetryDisabled;

/// A macro to send metric updates via a telemetry handle,
/// only if the `telemetry` feature is enabled.
/// Otherwise, it compiles to a no-op which still
/// references the given field to avoid dead_code
/// warnings.
///
/// ## Note
/// The macro imports `ibc_telemetry::MetricUpdate` into scope and all its variants.
///
/// ## Example
///
/// ```rust,ignore
/// metric!(self.telemetry, TxCount(1));
/// ```
#[macro_export]
macro_rules! metric {
    ($e:expr) => {
        #[cfg(feature = "telemetry")]
        #[allow(unused_imports)]
        {
            use ibc_telemetry::state::WorkerType;
            $e;
        }
    };
}
