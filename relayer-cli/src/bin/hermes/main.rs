//! Main entry point for Cli

#![deny(warnings, missing_docs, trivial_casts, unused_qualifications)]
#![forbid(unsafe_code)]

use ibc_relayer_cli::application::APPLICATION;

/// Boot Cli
fn main() -> eyre::Result<()> {
    if compact_logs() {
        oneline_eyre::install()?;
    } else {
        color_eyre::install()?;
    }

    abscissa_core::boot(&APPLICATION);
}

fn compact_logs() -> bool {
    let backtrace = std::option_env!("RUST_BACKTRACE").unwrap_or("");
    backtrace.is_empty() || backtrace == "0"
}
