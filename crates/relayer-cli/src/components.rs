//! Various components for internal use by the Abscissa subsystem.

use abscissa_core::{
    Component,
    FrameworkError,
    FrameworkErrorKind,
};
use ibc_relayer::{
    config::{
        Error,
        GlobalConfig,
        LogLevel,
    },
    util::debug_section::DebugSection,
};
use tracing_subscriber::{
    filter::EnvFilter,
    util::SubscriberInitExt,
    FmtSubscriber,
};

use crate::tracing_handle::ReloadHandle;

/// The name of the environment variable through which one can override
/// the tracing filter built in [`build_tracing_filter`].
const HERMES_LOG_VAR: &str = "RUST_LOG";

/// A custom component for parametrizing `tracing` in the relayer.
/// Primarily used for:
///
/// - Customizing the log output level, for filtering the output produced via tracing macros
///   (`debug!`, `info!`, etc.) or abscissa macros (`status_err`, `status_info`, etc.).
/// - Enabling JSON-formatted output without coloring
#[derive(Component, Debug)]
pub struct JsonTracing;

impl JsonTracing {
    /// Creates a new [`JsonTracing`] component
    pub fn new(cfg: GlobalConfig, debug_sections: &[DebugSection]) -> Result<Self, FrameworkError> {
        let filter = build_tracing_filter(cfg.log_level, debug_sections)?;
        // Note: JSON formatter is un-affected by ANSI 'color' option. Set to 'false'.
        let use_color = false;

        // Construct a tracing subscriber with the supplied filter and enable reloading.
        let builder = FmtSubscriber::builder()
            .with_target(false)
            .with_env_filter(filter)
            .with_writer(std::io::stdout)
            .with_ansi(use_color)
            .with_thread_ids(true)
            .json();

        let subscriber = builder.finish();
        subscriber.init();

        Ok(Self)
    }
}

#[derive(Component, Debug)]

/// A custom component for parametrizing `tracing` in the relayer.
/// Primarily used for:
///
/// - Customizing the log output level, for filtering the output produced via tracing macros
///   (`debug!`, `info!`, etc.) or abscissa macros (`status_err`, `status_info`, etc.).
/// - Enabling pretty output with coloring
pub struct PrettyTracing;

impl PrettyTracing {
    /// Creates a new [`PrettyTracing`] component
    pub fn new(cfg: GlobalConfig, debug_sections: &[DebugSection]) -> Result<Self, FrameworkError> {
        let filter = build_tracing_filter(cfg.log_level, debug_sections)?;

        // Construct a tracing subscriber with the supplied filter and enable reloading.
        let builder = FmtSubscriber::builder()
            .with_target(false)
            .with_env_filter(filter)
            .with_writer(std::io::stderr)
            .with_ansi(enable_ansi())
            .with_thread_ids(true);

        let subscriber = builder.finish();
        subscriber.init();

        Ok(Self)
    }

    pub fn new_with_reload_handle(
        cfg: GlobalConfig,
        debug_sections: &[DebugSection],
    ) -> Result<(Self, ReloadHandle<impl tracing::Subscriber + 'static>), FrameworkError> {
        let filter = build_tracing_filter(cfg.log_level, debug_sections)?;

        // Construct a tracing subscriber with the supplied filter and enable reloading.
        let builder = FmtSubscriber::builder()
            .with_target(false)
            .with_env_filter(filter)
            .with_writer(std::io::stderr)
            .with_ansi(enable_ansi())
            .with_thread_ids(true)
            .with_filter_reloading();

        let reload_handle = builder.reload_handle();

        let subscriber = builder.finish();
        subscriber.init();

        Ok((Self, reload_handle))
    }
}

/// Check if both stdout and stderr are proper terminal (tty),
/// so that we know whether or not to enable colored output,
/// using ANSI escape codes. If either is not, eg. because
/// stdout is redirected to a file, we don't enable colored output.
pub fn enable_ansi() -> bool {
    use std::io::IsTerminal;
    std::io::stdout().is_terminal() && std::io::stderr().is_terminal()
}

/// The relayer crates targeted by the default log level.
const TARGET_CRATES: [&str; 2] = ["ibc_relayer", "ibc_relayer_cli"];

/// Build a tracing directive setting the log level for the relayer crates to the
/// given `log_level`.
pub fn default_directive(log_level: LogLevel) -> String {
    use itertools::Itertools;

    TARGET_CRATES
        .iter()
        .map(|&c| format!("{c}={log_level}"))
        .join(",")
}

/// Builds a tracing filter based on the input `log_level`.
/// Enables tracing exclusively for the relayer crates.
/// Returns error if the filter failed to build.
fn build_tracing_filter(
    default_level: LogLevel,
    debug_sections: &[DebugSection],
) -> Result<EnvFilter, FrameworkError> {
    let mut directive =
        std::env::var(HERMES_LOG_VAR).unwrap_or_else(|_| default_directive(default_level));

    if debug_sections.contains(&DebugSection::Rpc) {
        // Enable debug tracing for the `tendermint_rpc` crate as well
        directive.push_str(",tendermint_rpc=debug");
    }

    // Build the filter directive
    match EnvFilter::try_new(&directive) {
        Ok(out) => Ok(out),
        Err(e) => {
            eprintln!(
                "ERROR: unable to initialize Hermes with log filtering directive {directive:?}: {e}"
            );

            Err(FrameworkErrorKind::ConfigError
                .context(Error::invalid_log_directive(directive, e))
                .into())
        }
    }
}
