use crate::core::traits::handlers::update_client::AnyUpdateClientHandler;
use crate::core::traits::messages::update_client::UpdateClientMessageHandler;
use crate::core::traits::stores::client_reader::AnyClientReader;
use crate::core::traits::stores::client_writer::AnyClientWriter;
use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::types::chain::OfaChainWrapper;

pub trait OfaChainComponents<Chain>
where
    Chain: OfaChain,
{
    type AnyClientReader: AnyClientReader<OfaChainWrapper<Chain>>;

    type AnyClientWriter: AnyClientWriter<OfaChainWrapper<Chain>>;

    type UpdateClientMessageHandler: UpdateClientMessageHandler<OfaChainWrapper<Chain>>;
}

pub trait OfaClientComponents<Chain>
where
    Chain: OfaChain,
{
    type AnyUpdateClientHandler: AnyUpdateClientHandler<OfaChainWrapper<Chain>>;
}
