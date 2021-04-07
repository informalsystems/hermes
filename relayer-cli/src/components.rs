use abscissa_core::{Component, FrameworkError};
use tracing_subscriber::fmt::{
    format::{Format, Json, JsonFields},
    time::SystemTime,
    Formatter,
};
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{reload::Handle, EnvFilter, FmtSubscriber};

use ibc_relayer::config::GlobalConfig;

/// Abscissa component for initializing the `tracing` subsystem
#[derive(Component, Debug)]
pub struct Tracing {
    filter_handle: Handle<EnvFilter, Formatter<JsonFields, Format<Json, SystemTime>>>,
}

/// A custom component for parametrizing `tracing` in the relayer. Primarily used for:
///     - customizes the log output level, for filtering the output produced via tracing macros
///         (`debug!`, `info!`, etc.) or abscissa macros (`status_err`, `status_info`, etc.).
///     - enables JSON-formatted output
impl Tracing {
    /// Creates a new [`Tracing`] component
    pub fn new(cfg: GlobalConfig) -> Result<Self, FrameworkError> {
        let filter = cfg.log_level;
        let use_color = false;

        // Construct a tracing subscriber with the supplied filter and enable reloading.
        let builder = FmtSubscriber::builder()
            .with_env_filter(filter)
            .with_ansi(use_color)
            .json()
            .with_filter_reloading();
        let filter_handle = builder.reload_handle();

        let subscriber = builder.finish();
        subscriber.init();

        Ok(Self { filter_handle })
    }
}
