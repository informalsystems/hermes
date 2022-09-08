//! Defines the `Async` trait for any data that can be sent
//! across async boundaries. Also provides a blanket implementation
//! of the `Async` trait.

pub trait Async: Sized + Send + Sync + 'static {}

impl<A> Async for A where A: Sized + Send + Sync + 'static {}
