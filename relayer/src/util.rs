mod block_on;
pub use block_on::block_on;

pub mod iter;
pub mod sled;

/// If a type `E` implements this, it means that `E` may sometimes return errors that are
/// unrecoverable.
///
/// ## Purpose
/// This trait allows for more concise code
pub trait Unrecoverable: Sized {
    /// Method is unreachable, no need to implement.
    fn conclude() -> Self {
        unimplemented!()
    }
}
