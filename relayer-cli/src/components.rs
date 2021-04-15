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
use tracing_subscriber::fmt::format::{DefaultFields, Full};

/// Custom types to simplify the `Tracing` definition below
type JsonFormatter = TracingFormatter<JsonFields, Format<Json, SystemTime>, StdWriter>;
type PrettyFormatter = TracingFormatter<DefaultFields, Format<Full, SystemTime>, StdWriter>;
type StdWriter = fn() -> io::Stderr;

/// A custom component for parametrizing `tracing` in the relayer.
/// Primarily used for:
///
/// - Customizing the log output level, for filtering the output produced via tracing macros
///   (`debug!`, `info!`, etc.) or abscissa macros (`status_err`, `status_info`, etc.).
/// - Enabling JSON-formatted output without coloring
#[derive(Component, Debug)]
pub struct JsonTracing {
    filter_handle: Handle<EnvFilter, JsonFormatter>,
}

impl JsonTracing {
    /// Creates a new [`Tracing`] component
    #[allow(trivial_casts)]
    pub fn new(cfg: GlobalConfig) -> Result<Self, FrameworkError> {
        let filter = build_tracing_filter(cfg.log_level);
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

#[derive(Component, Debug)]
pub struct PrettyTracing {
    filter_handle: Handle<EnvFilter, PrettyFormatter>,
}

impl PrettyTracing {
    /// Creates a new [`Tracing`] component
    #[allow(trivial_casts)]
    pub fn new(cfg: GlobalConfig) -> Result<Self, FrameworkError> {
        let filter = build_tracing_filter(cfg.log_level);
        let use_color = false;

        // Construct a tracing subscriber with the supplied filter and enable reloading.
        let builder = FmtSubscriber::builder()
            .with_env_filter(filter)
            .with_writer(std::io::stderr as StdWriter)
            .with_ansi(use_color)
            .with_filter_reloading();

        let filter_handle = builder.reload_handle();

        let subscriber = builder.finish();
        subscriber.init();

        Ok(Self { filter_handle })
    }
}

fn build_tracing_filter(log_level: String) -> String {
    let target_crates = ["ibc_relayer", "ibc_relayer_cli"];

    target_crates
        .iter()
        .map(|&c| format!("{}={}", c, log_level))
        .reduce(|a, b| format!("{},{}", a, b))
        .unwrap()
}
