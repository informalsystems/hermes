pub trait Async: Sized + Send + Sync + 'static {}

impl<A> Async for A where A: Sized + Send + Sync + 'static {}
