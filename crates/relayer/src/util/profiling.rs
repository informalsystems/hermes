use std::fs::{File, OpenOptions};
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::sync::Mutex;

use once_cell::sync::OnceCell;
use serde_derive::Serialize;
use serde_json::Value;

std::thread_local! {
    pub static DEPTH: AtomicUsize = AtomicUsize::new(0);
}

static FILE: OnceCell<Mutex<File>> = OnceCell::new();
static ENABLED: AtomicUsize = AtomicUsize::new(0);

const CONSOLE_MASK: usize = 0b01;
const JSON_MASK: usize = 0b10;

pub fn enable(console: bool, json: bool) {
    let console_mask = if console { CONSOLE_MASK } else { 0 };
    let json_mask = if json { JSON_MASK } else { 0 };

    ENABLED.store(console_mask | json_mask, Relaxed);
}

pub fn console_enabled() -> bool {
    ENABLED.load(Relaxed) & CONSOLE_MASK != 0
}

pub fn json_enabled() -> bool {
    ENABLED.load(Relaxed) & JSON_MASK != 0
}

fn enabled() -> usize {
    ENABLED.load(Relaxed)
}

/// Measure the time between when this value is allocated
/// and when it is dropped.
pub struct Timer {
    name: &'static str,
    info: Value,
    start: std::time::Instant,
}

#[derive(Debug, Serialize)]
struct TimerInfo<'a> {
    name: &'a str,
    #[serde(flatten)]
    info: &'a Value,
    elapsed: u128,
}

impl Timer {
    pub fn new(name: &'static str, info: Value) -> Self {
        let depth = DEPTH.with(|d| d.fetch_add(1, Relaxed));
        let pad = "   ".repeat(depth);

        if console_enabled() {
            tracing::info!("{}⏳ {} - start", pad, name);
        }

        Self {
            name,
            info,
            start: std::time::Instant::now(),
        }
    }
}

impl Drop for Timer {
    fn drop(&mut self) {
        let enabled = enabled();

        if enabled == 0 {
            return;
        }

        let elapsed = self.start.elapsed().as_millis();

        let depth = DEPTH.with(|d| d.fetch_sub(1, Relaxed));
        let pad = "   ".repeat(depth - 1);

        if enabled & CONSOLE_MASK != 0 {
            tracing::info!("{}⏳ {} - elapsed: {}ms", pad, self.name, elapsed);
        }

        if enabled & JSON_MASK != 0 {
            output_json(&TimerInfo {
                name: self.name,
                info: &self.info,
                elapsed,
            });
        }
    }
}

pub fn open_or_create_profile_file(file_name: &Path) {
    let file = OpenOptions::new()
        .append(true)
        .create(true)
        .open(file_name)
        .unwrap();

    match FILE.set(Mutex::new(file)) {
        Ok(_) => tracing::trace!("profile file created at: {file_name:#?}"),
        Err(e) => tracing::error!(
            "profile file was already set with: {:#?}",
            e.lock().unwrap().metadata()
        ),
    }
}

fn output_json(info: &TimerInfo<'_>) {
    if let Some(f) = FILE.get() {
        if let Err(e) = _output_json(f, info) {
            tracing::error!("couldn't write to file: {e}");
        }
    } else {
        tracing::debug!("File for profiling output is not set");
    }
}

fn _output_json(f: &Mutex<File>, info: &TimerInfo<'_>) -> Result<(), Box<dyn std::error::Error>> {
    use std::io::Write;

    let mut f = f.lock().unwrap();
    serde_json::to_writer(&mut *f, info)?;
    writeln!(&mut *f)?;

    Ok(())
}

/// Measure the time until the current scope ends.
///
/// Only enabled when "--debug=profiling" is set.
///
/// ## Example
///
/// ```rust
/// use ibc_relayer::time;
///
/// let val1 = 1;
/// let val2 = 2;
/// time!("full scope", {"id1": val1, "id2": val2});
///
/// let x = {
///   time!("inner scope", {});
///
///   42
///   // "inner scope" timer ends here
/// };
/// // "full scope" timer ends here
/// ```
#[macro_export]
macro_rules! time {
    ($name:expr, $info:tt) => {
        let _timer = $crate::util::profiling::Timer::new($name, ::serde_json::json!($info));
    };

    ($name:expr) => {
        let _timer = $crate::util::profiling::Timer::new($name, ::serde_json::json!({}));
    };
}
