use core::marker::PhantomData;

use crate::all_for_one::traits::base::AfoChainContext;
use crate::core::impls::message_handlers::dispatch::DispatchIbcMessages;
use crate::core::impls::message_handlers::update_client::BaseUpdateClientMessageHandler;
use crate::core::traits::message_handler::MessageHandler;
use crate::core::traits::messages::update_client::UpdateClientMessageHandler;

pub fn can_build_base_update_client_message_handler<Context>(
) -> PhantomData<impl UpdateClientMessageHandler<Context>>
where
    Context: AfoChainContext,
{
    PhantomData::<BaseUpdateClientMessageHandler>
}

pub fn can_build_dispatch_ibc_message_handler<Context>() -> PhantomData<impl MessageHandler<Context>>
where
    Context: AfoChainContext,
{
    PhantomData::<DispatchIbcMessages>
}
