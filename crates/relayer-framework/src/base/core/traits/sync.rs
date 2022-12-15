/**
   This is defined as a convenient constraint alias to
   `Sized + Send + Sync + 'static`.

   This constraint is commonly required to be present in almost all associated
   types. The `Sized` constraint is commonly required for associated types to be
   used as generic parameters. The `Send + Sync + 'static` constraints are
   important for the use of async functions inside traits.

   Because Rust do not currently natively support the use of async functions
   in traits, we use the [`async_trait`] crate to desugar async functions
   inside traits into functions returning
   `Pin<Box<dyn Future + Send>>`. Due to the additional `Send` and lifetime
   trait bounds inside the returned boxed future, almost all values that are
   used inside the async functions are required to have types that implement
   `Send` and `Sync`.

   It is also common to require the associated types to have the `'static`
   lifetime for them to be used inside async functions, because Rust would
   otherwise infer a more restrictive lifetime that does not outlive the
   async functions. The `'static` lifetime constraint here really means
   that the types implementing `Async` must not contain any lifetime
   parameter.
*/
pub trait Async: Sized + Send + Sync + 'static {}

impl<A> Async for A where A: Sized + Send + Sync + 'static {}
