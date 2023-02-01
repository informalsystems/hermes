use crate::core::traits::error::HasError;
use crate::core::traits::message::HasMessageMethods;
use crate::core::traits::message_handler::MessageHandler;
use crate::core::traits::messages::update_client::{
    HasUpdateClientMessage, HasUpdateClientMessageHandler,
};

pub struct DispatchIbcMessages;

pub trait InjectDispatchError: HasMessageMethods + HasError {
    fn unknown_message_error(message_type: &Self::MessageType) -> Self::Error;

    fn parse_message_error(message_type: &Self::MessageType) -> Self::Error;
}

impl<Context> MessageHandler<Context> for DispatchIbcMessages
where
    Context: HasMessageMethods,
    Context: HasUpdateClientMessageHandler,
    Context: InjectDispatchError,
{
    fn handle_message(context: &Context, message: &Context::Message) -> Result<(), Context::Error> {
        let message_type = Context::message_type(message);

        // TODO: Handle all IBC messages here

        if message_type == <Context as HasUpdateClientMessage>::MESSAGE_TYPE {
            let update_client_message = Context::try_extract_update_client_message(message)
                .ok_or_else(|| Context::parse_message_error(&message_type))?;

            context.handle_update_client_message(update_client_message)?;

            Ok(())
        } else {
            Err(Context::unknown_message_error(&message_type))
        }
    }
}
