//! Cli Config
//!
//! See instructions in `commands.rs` to specify the path to your
//! application's configuration file and/or command-line options
//! for specifying it.

use std::path::PathBuf;

use abscissa_core::{error::BoxError, EntryPoint, Options};

use crate::commands::CliCmd;

pub use relayer::config::Config;

/// Get the path to configuration file
pub fn config_path() -> Result<PathBuf, BoxError> {
    let mut args = std::env::args();
    assert!(args.next().is_some(), "expected one argument but got zero");
    let args = args.collect::<Vec<_>>();
    let app = EntryPoint::<CliCmd>::parse_args_default(args.as_slice())?;
    let config_path = app.config.ok_or_else(|| "no config file specified")?;
    Ok(config_path)
}
