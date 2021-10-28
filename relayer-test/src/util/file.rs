use std::fs;
use std::io;
use std::thread;

use crate::error::Error;

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
