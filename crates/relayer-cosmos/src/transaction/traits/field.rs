pub trait HasField<Field> {
    fn get_field(&self) -> &Field;
}

pub trait FieldGetter<Context> {
    fn get_from(context: &Context) -> &Self;
}

impl<Context, Field> FieldGetter<Context> for Field
where
    Context: HasField<Field>,
{
    fn get_from(context: &Context) -> &Self {
        context.get_field()
    }
}
