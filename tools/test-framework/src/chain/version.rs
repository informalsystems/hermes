use semver::Version;
use tracing::debug;

use crate::chain::exec::simple_exec;
use crate::error::{handle_generic_error, Error};

pub fn get_chain_command_version(command: &str) -> Result<Version, Error> {
    let output = simple_exec("version-command", command, &["version"])?;

    // gaia6 somehow outputs version string result in STDERR
    let raw_version_str = if output.stdout.is_empty() {
        output.stderr
    } else {
        output.stdout
    };

    let version_str = match raw_version_str.strip_prefix('v') {
        Some(str) => str.trim(),
        None => raw_version_str.trim(),
    };

    debug!("parsing version string: {}", version_str);

    let version = Version::parse(version_str).map_err(handle_generic_error)?;

    Ok(version)
}
