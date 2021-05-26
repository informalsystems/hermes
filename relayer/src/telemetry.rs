#[macro_export]
macro_rules! metric {
    ($t:expr, $e:expr) => {
        #[cfg(feature = "telemetry")]
        $t.send($e);
    };
}
