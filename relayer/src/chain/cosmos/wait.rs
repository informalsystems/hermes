use crate::util::retry::Fixed;
use core::time::Duration;

pub fn wait_for_block_commits(max_total_wait: Duration) -> impl Iterator<Item = Duration> {
    let backoff_millis = 300; // The periodic backoff
    let count: usize = (max_total_wait.as_millis() / backoff_millis as u128) as usize;
    Fixed::from_millis(backoff_millis).take(count)
}
