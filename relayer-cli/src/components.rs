use std::io;

use abscissa_core::component::Id;
use abscissa_core::{Component, FrameworkError};
use tracing_subscriber::fmt::{
    format::{Format, Json, JsonFields},
    time::SystemTime,
    Formatter as TracingFormatter,
};
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{reload::Handle, EnvFilter, FmtSubscriber};

use ibc_relayer::config::GlobalConfig;

pub const TRACING_COMPONENT_ID: Id = Id::new("ibc_relayer_cli::components::Tracing");

/// Custom types to simplify the `Tracing` definition below
type Formatter = TracingFormatter<JsonFields, Format<Json, SystemTime>, StdWriter>;
type StdWriter = fn() -> io::Stderr;

/// Abscissa component for initializing the `tracing` subsystem
#[derive(Component, Debug)]
pub struct Tracing {
    filter_handle: Handle<EnvFilter, Formatter>,
}

/// A custom component for parametrizing `tracing` in the relayer. Primarily used for:
///     - customizes the log output level, for filtering the output produced via tracing macros
///         (`debug!`, `info!`, etc.) or abscissa macros (`status_err`, `status_info`, etc.).
///     - enables JSON-formatted output
impl Tracing {
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
