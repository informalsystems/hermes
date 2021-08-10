//! Main entry point for Cli

#![deny(warnings, missing_docs, trivial_casts, unused_qualifications)]
#![forbid(unsafe_code)]

use ibc_relayer_cli::application::APPLICATION;

/// Boot Cli
fn main() -> eyre::Result<()> {
    color_eyre::install()?;
    abscissa_core::boot(&APPLICATION);
}
