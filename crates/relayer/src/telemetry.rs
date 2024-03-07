// If the `telemetry` feature is enabled, re-export the `ibc-telemetry` state.
pub type Telemetry = alloc::sync::Arc<ibc_telemetry::TelemetryState>;

/// A macro to send metric updates via a telemetry handle,
/// only if the `telemetry` feature is enabled.
/// Otherwise, it compiles to a no-op.
///
/// The macro can be used in two ways:
///
/// a) By passing it an arbitrary expression as its single argument.
///
/// ```rust,ignore
/// telemetry!(ibc_telemetry::global().tx_count(chain.id(), 1));
/// ```
///
/// b) In the common case where one wants to update a metric,
///    the macro accepts the metric's name, followed by its arguments.
///
/// ```rust,ignore
/// telemetry!(tx_count, chain.id(), 1);
/// ```
///
#[macro_export]
macro_rules! telemetry {
    ($id:ident, $($args:expr),* $(,)*) => {
        #[allow(unused_imports, unused_variables)]
        {
            use ::ibc_telemetry::state::WorkerType;

            ::ibc_telemetry::global().$id($($args),*);
        }
    };

    ($e:expr) => {
        #[allow(unused_imports, unused_variables)]
        {
            use ::ibc_telemetry::state::WorkerType;

            $e;
        }
    };
}
