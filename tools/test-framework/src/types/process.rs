/*!
   Define wrapper type around [`std::process::Child`] to kill the
   child process when the value is dropped.
*/

use eyre::Report as Error;
use std::process::Child;

/**
   A lightweight wrapper around std::process::Child to ensure that the
   process is killed when the handle is dropped.
*/
pub struct ChildProcess {
    child: Child,
    waited: bool,
}

impl ChildProcess {
    /// Create a new [`ChildProcess`] from the primitive [`Child`] type.
    pub fn new(child: Child) -> Self {
        Self {
            child,
            waited: false,
        }
    }

    /// Wait for the child process to terminate.
    pub fn wait(&mut self) -> Result<(), Error> {
        if !self.waited {
            self.waited = true;
            self.child.wait()?;
        }

        Ok(())
    }

    /// Kill the underlying child process.
    pub fn kill(&mut self) -> Result<(), Error> {
        self.child.kill()?;
        self.wait()?;

        Ok(())
    }
}

impl Drop for ChildProcess {
    fn drop(&mut self) {
        if !self.waited {
            let _ = self.kill();
        }
    }
}
