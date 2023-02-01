use crate::core::traits::events::misbehavior::InjectMisbehaviorEvent;
use crate::core::traits::events::update_client::InjectUpdateClientEvent;

pub trait AfoEventContext: InjectUpdateClientEvent + InjectMisbehaviorEvent {}

impl<Context> AfoEventContext for Context where
    Context: InjectUpdateClientEvent + InjectMisbehaviorEvent
{
}
