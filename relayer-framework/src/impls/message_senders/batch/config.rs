use core::time::Duration;

#[derive(Debug, Clone)]
pub struct BatchConfig {
    pub max_message_count: usize,
    pub max_tx_size: usize,
    pub buffer_size: usize,
    pub max_delay: Duration,
    pub sleep_time: Duration,
}

impl Default for BatchConfig {
    fn default() -> Self {
        Self {
            max_message_count: 10,
            max_tx_size: 1000,
            buffer_size: 1000,
            max_delay: Duration::from_secs(1),
            sleep_time: Duration::from_millis(50),
        }
    }
}
