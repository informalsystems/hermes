use crate::chain::exec::simple_exec;
use crate::error::Error;
use crate::prelude::handle_generic_error;

pub fn major_version(command_path: &str) -> Result<u64, Error> {
    let output = simple_exec("version", command_path, &["version"])?;

    // The version seems to be returned in stderr
    match output.stderr.chars().nth(1) {
        Some(major_version) => major_version
            .to_string()
            .parse::<u64>()
            .map_err(handle_generic_error),
        None => Ok(0),
    }
}
