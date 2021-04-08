use std::io;

use abscissa_core::{Component, FrameworkError};
use tracing_subscriber::{
    fmt::{
        format::{Format, Json, JsonFields},
        time::SystemTime,
        Formatter as TracingFormatter,
    },
    reload::Handle,
    util::SubscriberInitExt,
    EnvFilter, FmtSubscriber,
};

use ibc_relayer::config::GlobalConfig;

/// Custom types to simplify the `Tracing` definition below
type Formatter = TracingFormatter<JsonFields, Format<Json, SystemTime>, StdWriter>;
type StdWriter = fn() -> io::Stderr;

/// A custom component for parametrizing `tracing` in the relayer.
/// Primarily used for:
///
/// - Customizing the log output level, for filtering the output produced via tracing macros
///   (`debug!`, `info!`, etc.) or abscissa macros (`status_err`, `status_info`, etc.).
/// - Enabling JSON-formatted output without coloring
#[derive(Component, Debug)]
pub struct JsonTracing {
    filter_handle: Handle<EnvFilter, Formatter>,
}

impl JsonTracing {
    /// Creates a new [`Tracing`] component
    #[allow(trivial_casts)]
    pub fn new(cfg: GlobalConfig) -> Result<Self, FrameworkError> {
        let filter = cfg.log_level;
        let use_color = false;

        // Construct a tracing subscriber with the supplied filter and enable reloading.
        let builder = FmtSubscriber::builder()
            .with_env_filter(filter)
            .with_writer(std::io::stderr as StdWriter)
            .with_ansi(use_color)
            .json()
            .with_filter_reloading();

        let filter_handle = builder.reload_handle();

        let subscriber = builder.finish();
        subscriber.init();

        Ok(Self { filter_handle })
    }
}
