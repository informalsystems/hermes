#[cfg(feature = "profiling")]
pub mod profiling {

    use core::sync::atomic::AtomicUsize;
    use core::sync::atomic::Ordering::Relaxed;
    use once_cell::sync::OnceCell;
    use serde_derive::Serialize;
    use serde_json::Value;
    use std::fs::File;
    use std::fs::OpenOptions;
    use std::path::Path;

    std::thread_local! {
        pub static DEPTH: AtomicUsize = AtomicUsize::new(0);
    }
    static FILE: OnceCell<File> = OnceCell::new();

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

            tracing::info!("{}⏳ {} - start", pad, name);

            Self {
                name,
                info,
                start: std::time::Instant::now(),
            }
        }
    }

    impl Drop for Timer {
        fn drop(&mut self) {
            let elapsed = self.start.elapsed().as_millis();

            let depth = DEPTH.with(|d| d.fetch_sub(1, Relaxed));
            let pad = "   ".repeat(depth - 1);

            tracing::info!("{}⏳ {} - elapsed: {}ms", pad, self.name, elapsed);

            let info = TimerInfo {
                name: self.name,
                info: &self.info,
                elapsed,
            };

            to_json_format(&info);
        }
    }

    pub fn open_or_create_profile_file(file_name: &Path) {
        let file = OpenOptions::new()
            .write(true)
            .append(true)
            .create(true)
            .open(file_name)
            .unwrap();

        match FILE.set(file) {
            Ok(_) => tracing::trace!("profile file created at: {file_name:#?}"),
            Err(e) => tracing::error!("profile file was already set with: {:#?}", e.metadata()),
        }
    }

    fn to_json_format(info: &TimerInfo<'_>) {
        match FILE.get() {
            Some(mut f) => {
                if let Err(e) = serde_json::to_writer(&mut f, &info) {
                    tracing::error!("Couldn't write to file: {e}");
                }
            }
            None => tracing::debug!("File for profiling is not set"),
        }
    }
}

/// Measure the time until the current scope ends.
///
/// Only enabled when the "profiling" feature is enabled.
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
        #[cfg(feature = "profiling")]
        let _timer = $crate::macros::profiling::Timer::new($name, ::serde_json::json!($info));
    };

    ($name:expr) => {
        #[cfg(feature = "profiling")]
        let _timer = $crate::macros::profiling::Timer::new($name, ::serde_json::json!({}));
    };
}
