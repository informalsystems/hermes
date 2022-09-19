/*!
   Filesystem utilities.
*/

use std::fs;
use std::io;
use std::thread;

use crate::error::Error;

/**
   Pipe a streaming source implementing [`std::io::Read`] to a file in
   append mode.

   This is used to pipe log output from a full node's child process
   to log files.
*/
pub fn pipe_to_file(
    mut source: impl io::Read + Send + 'static,
    file_path: &str,
) -> Result<(), Error> {
    let mut file = fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open(file_path)?;

    thread::spawn(move || {
        std::io::copy(&mut source, &mut file).unwrap();
    });

    Ok(())
}
