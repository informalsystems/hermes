use std::path::PathBuf;

use crate::prelude::app_reader;

/// Get the path to configuration file
pub fn config_path() -> Option<PathBuf> {
    let app = app_reader();
    app.config_path().cloned()
}
