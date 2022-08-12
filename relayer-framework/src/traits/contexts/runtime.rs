use crate::traits::contexts::error::ErrorContext;

pub trait RuntimeContext: ErrorContext {
    type Runtime: ErrorContext<Error = Self::Error>;

    fn runtime(&self) -> &Self::Runtime;
}
