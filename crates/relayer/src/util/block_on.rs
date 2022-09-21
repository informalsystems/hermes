//! Utility function to execute a future synchronously

use futures::Future;

/// Spawns a new tokio runtime and use it to block on the given future.
pub fn block_on<F: Future>(future: F) -> F::Output {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
        .block_on(future)
}
