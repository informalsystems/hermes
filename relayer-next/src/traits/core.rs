pub trait CoreTraits: Sized + Send + Sync + 'static {}

impl<A> CoreTraits for A where A: Sized + Send + Sync + 'static {}
