use crate::util::retry::{clamp_total, ConstantGrowth};
use core::time::Duration;

/// A basic worker retry strategy.
///
/// The backoff delay is initially 200ms and grows
/// by 100ms at each step. The backoff delay is
/// capped at 500ms.
/// The overall amount of time spent backing off
/// is capped to 2 seconds.
/// See the `default_strategy` test below.
pub fn worker_default_strategy() -> impl Iterator<Item = Duration> {
    let strategy = ConstantGrowth::new(Duration::from_millis(200), Duration::from_millis(100));
    clamp_total(strategy, Duration::from_millis(500), Duration::from_secs(2))
}

/// A stubborn worker retry strategy.
///
/// Initial retry backoff is hardcoded to 1s, and
/// this delay grows very slowly and steadily by
/// 10ms at every step. The strategy delay is
/// not capped, so it will retry indefinitely.
///
/// See the `stubbord_strategy` test below.
pub fn worker_stubborn_strategy() -> impl Iterator<Item = Duration> {
    ConstantGrowth::new(Duration::from_secs(1), Duration::from_millis(10))
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use crate::worker::retry_strategy::{worker_default_strategy, worker_stubborn_strategy};

    #[test]
    fn default_strategy() {
        let strategy = worker_default_strategy();
        let delays = strategy.take(10).collect::<Vec<_>>();
        // This strategy has exactly 6 retry steps
        assert_eq!(
            delays,
            vec![
                Duration::from_millis(200),
                Duration::from_millis(300),
                Duration::from_millis(400),
                Duration::from_millis(500),
                Duration::from_millis(500),
                Duration::from_millis(100),
            ]
        );
    }

    #[test]
    fn stubborn_strategy() {
        let strategy = worker_stubborn_strategy();
        // This strategy has an infinite amount of retry steps
        // Assert that delays increment by 10ms
        // Stop after 50 iterations
        let mut delaysp = strategy.into_iter().take(50).peekable();
        let step = Duration::from_millis(10);
        while let Some(first) = delaysp.next() {
            if let Some(next) = delaysp.peek() {
                assert_eq!(first + step, *next);
            }
        }
    }
}
