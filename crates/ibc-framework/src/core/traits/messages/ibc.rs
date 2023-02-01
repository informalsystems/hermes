use crate::core::traits::messages::update_client::HasUpdateClientMessage;

pub trait HasIbcMessages: HasUpdateClientMessage {}

impl<Context> HasIbcMessages for Context where Context: HasUpdateClientMessage {}
