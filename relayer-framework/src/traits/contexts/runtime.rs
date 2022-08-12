use crate::traits::contexts::error::HasError;

pub trait HasRuntime: HasError {
    type Runtime: HasError<Error = Self::Error>;

    fn runtime(&self) -> &Self::Runtime;
}
