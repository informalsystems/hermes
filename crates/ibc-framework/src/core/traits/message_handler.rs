use crate::core::traits::error::HasError;
use crate::core::traits::message::HasMessageTypes;

pub trait MessageHandler<Context>
where
    Context: HasMessageTypes + HasError,
{
    fn handle_message(context: &Context, message: &Context::Message) -> Result<(), Context::Error>;
}
