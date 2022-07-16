mod sealed {
    pub trait SealedToBoxed<T: ?Sized> {}
    impl<T, U: Clone + Into<T>> SealedToBoxed<T> for U {}
    pub trait SealedTryFromIfSized<T> {}
    impl<T, U: TryFrom<T>> SealedTryFromIfSized<T> for U {}
}

pub trait ToBoxed<T: ?Sized>: sealed::SealedToBoxed<T> {
    fn to_boxed(&self) -> Box<T>;
}

impl<T, U: Clone + Into<T>> ToBoxed<T> for U {
    fn to_boxed(&self) -> Box<T> {
        Box::new(self.clone().into())
    }
}

pub trait TryFromIfSized<T>: sealed::SealedTryFromIfSized<T> {
    type Error;

    fn try_from(t: T) -> Result<Self, Self::Error>
    where
        Self: Sized;
}

impl<T, U: TryFrom<T>> TryFromIfSized<T> for U {
    type Error = <Self as TryFrom<T>>::Error;

    fn try_from(t: T) -> Result<Self, Self::Error>
    where
        Self: Sized,
    {
        <Self as TryFrom<T>>::try_from(t)
    }
}
