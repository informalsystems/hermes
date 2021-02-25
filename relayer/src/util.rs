mod block_on;
pub use block_on::block_on;

pub mod iter;
pub mod sled;

/// If a type `D` implements this, it means that `D` may sometimes appear alongside an error `E`
/// in `Result<D,E>` where the error is unrecoverable. See the documentation for method
/// `exit_with_unrecoverable_error` on how to use this trait.
///
/// ## Purpose
/// This trait allows for more concise code
pub trait Unrecoverable: Sized {
    /// Method is unreachable, no need to implement.
    fn conclude() -> Self {
        unimplemented!()
    }
}
