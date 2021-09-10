use crate::util::retry::{clamp_total, clamp, ConstantGrowth};
use std::time::Duration;


/// A basic worker retry strategy.
///
/// The delay is initially 200ms and grows
/// by 100ms at each step. The delay is
/// capped at 500ms.
/// The overall amount of time spent retrying
/// is capped to 2 seconds.
/// See the `default_strategy` test below.
pub fn worker_default_strategy() -> impl Iterator<Item = Duration> {
    let strategy = ConstantGrowth::new(Duration::from_millis(200), Duration::from_millis(100));
    clamp_total(strategy, Duration::from_millis(500), Duration::from_secs(2))
}


/// A stubborn worker retry strategy.
///
/// Initial retry delay is hardcoded to 1s, and
/// the delay grows by 1s at every step. The
/// strategy delay is capped at 60 sec. The
/// total number of retries is capped to 400.
/// Therefore the overall amount of time spent
/// retrying will be approx. 6 hours.
///
/// See the `stubbord_strategy` test below.
pub fn worker_stubborn_strategy() -> impl Iterator<Item = Duration> {
    let strategy = ConstantGrowth::new(Duration::from_secs(1), Duration::from_secs(1));
    clamp(strategy, Duration::from_secs(60), 400)
}


#[cfg(test)]
mod tests {
    use std::time::Duration;

    use crate::worker::retry_strategy::{worker_stubborn_strategy, worker_default_strategy};

    #[test]
    fn default_strategy() {
        let strategy = worker_default_strategy();
        let delays = strategy.take(10).collect::<Vec<_>>();
        assert_eq!(delays,
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
        let delays = strategy.collect::<Vec<_>>();
        assert_eq!(delays.len(), 400);

        // Assert the first 10 steps manually
        assert_eq!(delays.iter().take(10).cloned().collect::<Vec<_>>(),
            vec![
                Duration::from_secs(1),
                Duration::from_secs(2),
                Duration::from_secs(3),
                Duration::from_secs(4),
                Duration::from_secs(5),
                Duration::from_secs(6),
                Duration::from_secs(7),
                Duration::from_secs(8),
                Duration::from_secs(9),
                Duration::from_secs(10),
            ]
        );

        // Assert that delays increment by 1s and are capped to 60s
        let mut delaysp = delays.into_iter().peekable();
        let cap = Duration::from_secs(60);
        let step = Duration::from_secs(1);
        for first in delaysp.next() {
            if let Some(next) = delaysp.peek() {
                if first == cap {
                    assert_eq!(*next, cap);
                } else {
                    assert_eq!(first + step, *next);
                }
            }
        }
    }
}