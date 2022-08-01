use crate::traits::core::ErrorContext;

pub trait RuntimeContext: ErrorContext {
    type Runtime: ErrorContext<Error = Self::Error>;

    fn runtime(&self) -> &Self::Runtime;
}
