use alloc::boxed::Box;
use core::convert::{Into as CoreInto, TryFrom as CoreTryFrom};

pub trait Into<T: ?Sized> {
    fn into(&self) -> Box<T>;
}

impl<T, U: Clone + CoreInto<T>> Into<T> for U {
    fn into(&self) -> Box<T> {
        Box::new(self.clone().into())
    }
}

pub trait TryFrom<T> {
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
