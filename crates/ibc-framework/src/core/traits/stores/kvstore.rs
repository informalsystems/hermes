use crate::core::traits::error::HasError;
use crate::core::traits::sync::Async;

pub trait ReadOnlyKvStore<Key, Value>: HasError
where
    Key: Async,
    Value: Async,
{
    fn has(key: &Key) -> Result<bool, Self::Error>;

    fn get(key: &Key) -> Result<Option<Value>, Self::Error>;
}

pub trait ReadWriteKvStore<Key, Value>: ReadOnlyKvStore<Key, Value>
where
    Key: Async,
    Value: Async,
{
    fn set(key: &Key, value: &Value) -> Result<(), Self::Error>;
}
