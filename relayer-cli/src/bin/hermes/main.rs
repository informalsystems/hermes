//! Main entry point for Cli

#![deny(warnings, missing_docs, trivial_casts, unused_qualifications)]
#![forbid(unsafe_code)]

use ibc_relayer_cli::application::APPLICATION;

fn main() -> eyre::Result<()> {
    install_error_reporter()?;

    abscissa_core::boot(&APPLICATION);
}

fn install_error_reporter() -> eyre::Result<()> {
    if !backtrace_enabled() {
        // If backtraces are disabled, display errors in single line.
        oneline_eyre::install()
    } else {
        // Otherwise, backtraces are enabled, so use the
        // default error report handler. The impl for
        // Application::framework_components takes care about
        // initialization of color_eyre.
        Ok(())
    }
}

fn backtrace_enabled() -> bool {
    match std::env::var("RUST_BACKTRACE").as_deref() {
        Ok("" | "0") | Err(_) => false,
        Ok(_) => true,
    }
}
