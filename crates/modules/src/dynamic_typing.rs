use core::any::Any;

pub trait AsAny: Any {
    fn as_any(&self) -> &dyn Any;
}

impl<M: Any> AsAny for M {
    fn as_any(&self) -> &dyn Any {
        self
    }
}
