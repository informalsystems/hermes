use alloc::boxed::Box;
use core::convert::{Into as CoreInto, TryFrom as CoreTryFrom};

mod sealed {
    use super::*;

    pub trait SealedInto<T: ?Sized> {}
    impl<T, U: Clone + CoreInto<T>> SealedInto<T> for U {}
    pub trait SealedTryFrom<T> {}
    impl<T, U: CoreTryFrom<T>> SealedTryFrom<T> for U {}
}

pub trait Into<T: ?Sized>: sealed::SealedInto<T> {
    fn into(&self) -> Box<T>;
}

impl<T, U: Clone + CoreInto<T>> Into<T> for U {
    fn into(&self) -> Box<T> {
        Box::new(self.clone().into())
    }
}

pub trait TryFrom<T>: sealed::SealedTryFrom<T> {
    type Error;

    fn try_from(t: T) -> Result<Self, Self::Error>
    where
        Self: Sized;
}

impl<T, U: CoreTryFrom<T>> TryFrom<T> for U {
    type Error = <Self as CoreTryFrom<T>>::Error;

    fn try_from(t: T) -> Result<Self, Self::Error>
    where
        Self: Sized,
    {
        <Self as CoreTryFrom<T>>::try_from(t)
    }
}
