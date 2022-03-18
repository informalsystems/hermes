use crate::util::retry::Fixed;
use core::time::Duration;

// Maximum number of retries for send_tx in the case of
// an account sequence mismatch at broadcast step.
pub const MAX_ACCOUNT_SEQUENCE_RETRY: u32 = 1;

// Backoff multiplier to apply while retrying in the case
// of account sequence mismatch.
pub const BACKOFF_MULTIPLIER_ACCOUNT_SEQUENCE_RETRY: u64 = 300;

pub fn wait_for_block_commits(max_total_wait: Duration) -> impl Iterator<Item = Duration> {
    let backoff_millis = 300; // The periodic backoff
    let count: usize = (max_total_wait.as_millis() / backoff_millis as u128) as usize;
    Fixed::from_millis(backoff_millis).take(count)
}
