use ibc_relayer_framework::base::core::traits::sync::Async;

pub trait FieldKey: Async {
    type Value: Async;
}

pub trait HasField<Key: FieldKey>: Async {
    fn get_field(&self) -> &Key::Value;
}

pub trait FieldGetter<Context>: FieldKey
where
    Context: HasField<Self>,
{
    fn get_from(context: &Context) -> &Self::Value;
}

impl<Context, Key> FieldGetter<Context> for Key
where
    Context: HasField<Key>,
    Key: FieldKey,
{
    fn get_from(context: &Context) -> &Key::Value {
        context.get_field()
    }
}
