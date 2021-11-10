//! Main entry point for Cli

#![deny(warnings, missing_docs, trivial_casts, unused_qualifications)]
#![forbid(unsafe_code)]

use ibc_relayer_cli::application::APPLICATION;
use ibc_relayer_cli::components::enable_ansi;

/// Boot Cli
fn main() -> eyre::Result<()> {
    if compact_logs() {
        oneline_eyre::install()?;
    } else if enable_ansi() {
        color_eyre::install()?;
    }

    abscissa_core::boot(&APPLICATION);
}

fn compact_logs() -> bool {
    matches!(std::env::var("RUST_BACKTRACE").as_deref(), Ok("" | "0"))
}
