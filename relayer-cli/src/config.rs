//! Cli Config
//!
//! See instructions in `commands.rs` to specify the path to your
//! application's configuration file and/or command-line options
//! for specifying it.

use std::path::PathBuf;

use crate::application::app_reader;

pub use ibc_relayer::config::Config;

/// Get the path to configuration file
pub fn config_path() -> Option<PathBuf> {
    let app = app_reader();
    app.config_path().cloned()
}
