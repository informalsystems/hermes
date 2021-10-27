//! Main entry point for Cli

#![deny(warnings, missing_docs, trivial_casts, unused_qualifications)]
#![forbid(unsafe_code)]

use ibc_relayer_cli::application::APPLICATION;
use ibc_relayer_cli::components::enable_ansi;

/// Boot Cli
fn main() -> eyre::Result<()> {
    if enable_ansi() {
        color_eyre::install()?;
    }

    abscissa_core::boot(&APPLICATION);
}
