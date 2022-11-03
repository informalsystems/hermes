use eyre::eyre;
use std::process::Command;
use std::str;
use tracing::{debug, trace};

use crate::error::{handle_exec_error, handle_generic_error, Error};

pub struct ExecOutput {
    pub stdout: String,
    pub stderr: String,
}

pub fn simple_exec(desc: &str, command_path: &str, args: &[&str]) -> Result<ExecOutput, Error> {
    debug!(
        "Executing command for {}: {} {}",
        desc,
        command_path,
        itertools::join(args, " ")
    );

    let output = Command::new(command_path)
        .args(args)
        .output()
        .map_err(handle_exec_error(command_path))?;

    if output.status.success() {
        let stdout = str::from_utf8(&output.stdout)
            .map_err(handle_generic_error)?
            .to_string();

        let stderr = str::from_utf8(&output.stderr)
            .map_err(handle_generic_error)?
            .to_string();

        trace!(
            "command executed successfully with stdout: {}, stderr: {}",
            stdout,
            stderr
        );

        Ok(ExecOutput { stdout, stderr })
    } else {
        let message = str::from_utf8(&output.stderr).map_err(handle_generic_error)?;

        Err(Error::generic(eyre!(
            "command exited with error status {:?} and message: {}",
            output.status.code(),
            message
        )))
    }
}
