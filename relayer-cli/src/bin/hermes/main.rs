//! Main entry point for Cli

#![deny(warnings, missing_docs, trivial_casts, unused_qualifications)]
#![forbid(unsafe_code)]

use ibc_relayer_cli::application::APPLICATION;
use std::env;

/// Boot Cli
fn main() -> eyre::Result<()> {
    let term_var = env::var("TERM").unwrap_or_else(|_| "".to_string());

    // Use color_eyre to display error traces in terminals that support color
    if term_var == "xterm-256color" || term_var == "xterm-color" {
        color_eyre::install()?;
    }

    abscissa_core::boot(&APPLICATION);
}
