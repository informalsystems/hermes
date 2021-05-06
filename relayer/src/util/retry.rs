use std::time::Duration;

use retry::delay::Fibonacci;

// Default parameters for the retrying mechanism
pub const MAX_RETRIES: usize = 5;
pub const MAX_RETRY_DELAY: Duration = Duration::from_secs(5 * 60);
pub const INITIAL_RETRY_DELAY: Duration = Duration::from_secs(1);

#[derive(Copy, Clone, Debug)]
pub struct ConstantGrowth {
    delay: Duration,
    incr: Duration,
}

impl ConstantGrowth {
    pub const fn new(delay: Duration, incr: Duration) -> Self {
        Self { delay, incr }
    }

    pub const fn clamp(self, max_delay: Duration, max_retries: usize) -> Clamped<Self> {
        Clamped::new(self, max_delay, max_retries)
    }
}

impl From<Duration> for ConstantGrowth {
    fn from(delay: Duration) -> Self {
        Self::new(delay, Duration::from_secs(1))
    }
}

impl Iterator for ConstantGrowth {
    type Item = Duration;

    fn next(&mut self) -> Option<Duration> {
        let delay = self.delay;

        if let Some(next) = self.delay.checked_add(self.incr) {
            self.delay = next;
        }

        Some(delay)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Clamped<S> {
    pub strategy: S,
    pub max_delay: Duration,
    pub max_retries: usize,
}

impl Default for Clamped<Fibonacci> {
    fn default() -> Self {
        Self::new(
            Fibonacci::from(INITIAL_RETRY_DELAY),
            MAX_RETRY_DELAY,
            MAX_RETRIES,
        )
    }
}

impl<S> Clamped<S> {
    pub const fn new(strategy: S, max_delay: Duration, max_retries: usize) -> Self {
        Self {
            strategy,
            max_delay,
            max_retries,
        }
    }

    pub fn iter(self) -> impl Iterator<Item = Duration>
    where
        S: Iterator<Item = Duration>,
    {
        let Self {
            strategy,
            max_retries,
            max_delay,
        } = self;

        strategy
            .take(max_retries)
            .map(move |delay| delay.min(max_delay))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const CONST_STRATEGY: ConstantGrowth =
        ConstantGrowth::new(Duration::from_secs(1), Duration::from_millis(500));

    #[test]
    fn const_growth_no_clamp() {
        let delays = CONST_STRATEGY.take(10).collect::<Vec<_>>();
        assert_eq!(
            delays,
            vec![
                Duration::from_millis(1000),
                Duration::from_millis(1500),
                Duration::from_millis(2000),
                Duration::from_millis(2500),
                Duration::from_millis(3000),
                Duration::from_millis(3500),
                Duration::from_millis(4000),
                Duration::from_millis(4500),
                Duration::from_millis(5000),
                Duration::from_millis(5500)
            ]
        );
    }

    #[test]
    fn clamped_const_growth_max_delay() {
        let strategy = CONST_STRATEGY.clamp(Duration::from_secs(10), 10);
        let delays = strategy.iter().collect::<Vec<_>>();
        assert_eq!(
            delays,
            vec![
                Duration::from_millis(1000),
                Duration::from_millis(1500),
                Duration::from_millis(2000),
                Duration::from_millis(2500),
                Duration::from_millis(3000),
                Duration::from_millis(3500),
                Duration::from_millis(4000),
                Duration::from_millis(4500),
                Duration::from_millis(5000),
                Duration::from_millis(5500)
            ]
        );
    }

    #[test]
    fn clamped_const_growth_max_retries() {
        let strategy = CONST_STRATEGY.clamp(Duration::from_secs(10000), 5);
        let delays = strategy.iter().collect::<Vec<_>>();
        assert_eq!(
            delays,
            vec![
                Duration::from_millis(1000),
                Duration::from_millis(1500),
                Duration::from_millis(2000),
                Duration::from_millis(2500),
                Duration::from_millis(3000)
            ]
        );
    }
}
