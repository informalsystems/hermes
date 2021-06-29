use std::io;

use abscissa_core::{Component, FrameworkError, FrameworkErrorKind};
use tracing_subscriber::{
    fmt::{
        format::{DefaultFields, Format, Full, Json, JsonFields},
        time::SystemTime,
        Formatter as TracingFormatter,
    },
    reload::Handle,
    util::SubscriberInitExt,
    EnvFilter, FmtSubscriber,
};

use ibc_relayer::config::GlobalConfig;

use crate::config;

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
        let filter = build_tracing_filter(cfg.log_level.to_string())?;
        // Note: JSON formatter is un-affected by ANSI 'color' option. Set to 'false'.
        let use_color = false;

        // Construct a tracing subscriber with the supplied filter and enable reloading.
        let builder = FmtSubscriber::builder()
            .with_target(false)
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
        let filter = build_tracing_filter(cfg.log_level.to_string())?;

        // Construct a tracing subscriber with the supplied filter and enable reloading.
        let builder = FmtSubscriber::builder()
            .with_target(false)
            .with_env_filter(filter)
            .with_writer(std::io::stderr as StdWriter)
            .with_ansi(enable_ansi())
            .with_filter_reloading();

        let filter_handle = builder.reload_handle();

        let subscriber = builder.finish();
        subscriber.init();

        Ok(Self { filter_handle })
    }
}

/// Check if both stdout and stderr are proper terminal (tty),
/// so that we know whether or not to enable colored output,
/// using ANSI escape codes. If either is not, eg. because
/// stdout is redirected to a file, we don't enable colored output.
fn enable_ansi() -> bool {
    atty::is(atty::Stream::Stdout) && atty::is(atty::Stream::Stderr)
}

/// Builds a tracing filter based on the input `log_level`.
/// Enables tracing exclusively for the relayer crates.
/// Returns error if the filter failed to build.
fn build_tracing_filter(log_level: String) -> Result<EnvFilter, FrameworkError> {
    let target_crates = ["ibc_relayer", "ibc_relayer_cli"];

    // SAFETY: unwrap() below works as long as `target_crates` is not empty.
    let directive_raw = target_crates
        .iter()
        .map(|&c| format!("{}={}", c, log_level))
        .reduce(|a, b| format!("{},{}", a, b))
        .unwrap();

    // Build the filter directive
    match EnvFilter::try_new(directive_raw.clone()) {
        Ok(out) => Ok(out),
        Err(e) => {
            eprintln!(
                "Unable to initialize Hermes from filter directive {:?}: {}",
                directive_raw, e
            );
            let our_err = config::invalid_log_level_error(log_level, e);
            Err(FrameworkErrorKind::ConfigError.context(our_err).into())
        }
    }
}
