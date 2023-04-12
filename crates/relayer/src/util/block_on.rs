//! Utility function to execute a future synchronously

use std::thread::JoinHandle;

use futures::Future;

/// Spawns a new tokio runtime and use it to block on the given future.
pub fn block_on<F: Future>(future: F) -> F::Output {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
        .block_on(future)
}

/// Spawns a new tokio runtime in a new thread and use it to block on the given future.
pub fn spawn_blocking<F>(future: F) -> JoinHandle<F::Output>
where
    F: Future + Send + 'static,
    F::Output: Send,
{
    std::thread::spawn(move || {
        tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap()
            .block_on(future)
    })
}
