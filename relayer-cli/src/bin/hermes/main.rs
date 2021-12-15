//! Main entry point for Cli

#![deny(warnings, missing_docs, trivial_casts, unused_qualifications)]
#![forbid(unsafe_code)]

use ibc_relayer_cli::application::APPLICATION;
use ibc_relayer_cli::components::enable_ansi;

fn main() -> eyre::Result<()> {
    install_error_reporter()?;

    abscissa_core::boot(&APPLICATION);
}

fn install_error_reporter() -> eyre::Result<()> {
    if !backtrace_enabled() {
        // If backtraces are disabled, display errors in single line.
        oneline_eyre::install()
    } else if enable_ansi() {
        // Else, if backtraces are enabled and we are in a terminal
        // supporting color, display full error logs in color.
        color_eyre::install()
    } else {
        // Otherwise, backtraces are enabled and we are piping to logs, so use the
        // default error report handler, which displays multiline errors
        // without color.
        Ok(())
    }
}

fn backtrace_enabled() -> bool {
    match std::env::var("RUST_BACKTRACE").as_deref() {
        Ok("" | "0") | Err(_) => false,
        Ok(_) => true,
    }
}
