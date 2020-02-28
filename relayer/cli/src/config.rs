//! Cli Config
//!
//! See instructions in `commands.rs` to specify the path to your
//! application's configuration file and/or command-line options
//! for specifying it.

use serde::{Deserialize, Serialize};

/// Cli Configuration
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CliConfig {
    /// An example configuration section
    pub relayer_config: relayer::config::Config,

    /// Dummy config option
    pub dummy: (),
}

/// Default configuration settings.
///
/// Note: if your needs are as simple as below, you can
/// use `#[derive(Default)]` on CliConfig instead.
impl Default for CliConfig {
    fn default() -> Self {
        Self {
            relayer_config: relayer::config::Config::default(),
            dummy: (),
        }
    }
}
