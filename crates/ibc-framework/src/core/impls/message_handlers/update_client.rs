use crate::core::traits::client::HasAnyClientMethods;
use crate::core::traits::error::HasError;
use crate::core::traits::event::HasEventEmitter;
use crate::core::traits::events::misbehavior::InjectMisbehaviorEvent;
use crate::core::traits::events::update_client::InjectUpdateClientEvent;
use crate::core::traits::handlers::update_client::HasAnyUpdateClientHandler;
use crate::core::traits::host::{HasHostMethods, HasHostTypes};
use crate::core::traits::ibc::HasIbcTypes;
use crate::core::traits::messages::update_client::{
    HasUpdateClientMessage, UpdateClientMessageHandler,
};
use crate::core::traits::stores::client_reader::HasAnyClientReader;
use crate::core::traits::stores::client_writer::HasAnyClientWriter;

pub trait InjectUpdateClientError: HasError + HasIbcTypes + HasHostTypes {
    fn client_frozen_error(client_id: &Self::ClientId) -> Self::Error;

    fn client_expired_error(
        client_id: &Self::ClientId,
        current_time: &Self::Timestamp,
        latest_allowed_update_time: &Self::Timestamp,
    ) -> Self::Error;
}

pub struct BaseUpdateClientMessageHandler;

impl<Context> UpdateClientMessageHandler<Context> for BaseUpdateClientMessageHandler
where
    Context: HasUpdateClientMessage,
    Context: HasAnyClientReader,
    Context: HasAnyUpdateClientHandler,
    Context: HasAnyClientMethods,
    Context: InjectUpdateClientError,
    Context: HasHostMethods,
    Context: HasIbcTypes,
    Context: InjectUpdateClientEvent,
    Context: InjectMisbehaviorEvent,
    Context: HasEventEmitter,
    Context: HasAnyClientWriter,
{
    fn handle_update_client_message(
        context: &Context,
        message: &Context::UpdateClientMessage,
    ) -> Result<(), Context::Error> {
        let client_id = Context::message_client_id(message);
        let new_any_client_header = Context::message_client_header(message);

        let current_any_client_state = context.get_any_client_state(client_id)?;

        if Context::client_state_is_frozen(&current_any_client_state) {
            return Err(Context::client_frozen_error(client_id));
        }

        {
            let current_time = context.host_timestamp();

            let latest_consensus_state = context.get_latest_any_consensus_state(client_id)?;

            let last_updated_time = Context::consensus_state_timestamp(&latest_consensus_state);

            let trusting_period = Context::client_state_trusting_period(&current_any_client_state);

            let latest_allowed_update_time =
                Context::add_duration(&last_updated_time, &trusting_period);

            if current_time > latest_allowed_update_time {
                return Err(Context::client_expired_error(
                    client_id,
                    &current_time,
                    &latest_allowed_update_time,
                ));
            }
        }

        let (new_any_client_state, new_any_consensus_state) = context
            .check_client_header_and_update_state(
                client_id,
                &current_any_client_state,
                new_any_client_header,
            )?;

        context.set_any_client_state(client_id, &new_any_client_state)?;

        if Context::client_state_is_frozen(&new_any_client_state) {
            let event = Context::misbehavior_event(
                client_id,
                &Context::client_state_type(&new_any_client_state),
                &Context::client_header_height(new_any_client_header),
                new_any_client_header,
            );

            context.emit_event(&event);
        } else {
            context.set_any_consensus_state(client_id, &new_any_consensus_state)?;

            let event = Context::update_client_event(
                client_id,
                &Context::client_state_type(&new_any_client_state),
                &Context::client_header_height(new_any_client_header),
                new_any_client_header,
            );

            context.emit_event(&event);
        }

        Ok(())
    }
}
