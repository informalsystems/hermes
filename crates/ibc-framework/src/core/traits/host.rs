use crate::core::traits::sync::Async;

pub trait HasHostTypes: Async {
    type Height: Async;

    type Timestamp: Ord + Async;

    // Require non-negative duration
    type Duration: Ord + Async;
}

pub trait HasHostMethods: HasHostTypes {
    fn host_height(&self) -> Self::Height;

    fn host_timestamp(&self) -> Self::Timestamp;

    fn add_duration(time: &Self::Timestamp, duration: &Self::Duration) -> Self::Timestamp;
}
