use crate::core::impls::message_handlers::dispatch::InjectDispatchError;
use crate::core::impls::message_handlers::update_client::InjectUpdateClientError;
use crate::core::traits::client::InjectClientTypeMismatchError;
use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::types::chain::OfaChainWrapper;

impl<Chain> InjectClientTypeMismatchError for OfaChainWrapper<Chain>
where
    Chain: OfaChain,
{
    fn client_type_mismatch_error(expected_client_type: &Self::ClientType) -> Self::Error {
        Chain::client_type_mismatch_error(expected_client_type)
    }
}

impl<Chain> InjectDispatchError for OfaChainWrapper<Chain>
where
    Chain: OfaChain,
{
    fn unknown_message_error(message_type: &Self::MessageType) -> Self::Error {
        Chain::unknown_message_error(message_type)
    }

    fn parse_message_error(message_type: &Self::MessageType) -> Self::Error {
        Chain::parse_message_error(message_type)
    }
}

impl<Chain> InjectUpdateClientError for OfaChainWrapper<Chain>
where
    Chain: OfaChain,
{
    fn client_frozen_error(client_id: &Self::ClientId) -> Self::Error {
        Chain::client_frozen_error(client_id)
    }

    fn client_expired_error(
        client_id: &Self::ClientId,
        current_time: &Self::Timestamp,
        latest_allowed_update_time: &Self::Timestamp,
    ) -> Self::Error {
        Chain::client_expired_error(client_id, current_time, latest_allowed_update_time)
    }
}
