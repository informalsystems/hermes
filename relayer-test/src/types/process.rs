use eyre::Report as Error;
use std::process::Child;

// A lightweight wrapper around std::process::Child
// to ensure that the process is killed when the handle
// is dropped.
pub struct ChildProcess {
    child: Child,
    waited: bool,
}

impl ChildProcess {
    pub fn new(child: Child) -> Self {
        Self {
            child,
            waited: false,
        }
    }

    pub fn wait(&mut self) -> Result<(), Error> {
        if !self.waited {
            self.waited = true;
            self.child.wait()?;
        }

        Ok(())
    }

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
