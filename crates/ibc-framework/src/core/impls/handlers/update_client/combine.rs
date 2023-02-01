use core::marker::PhantomData;

use crate::core::impls::handlers::update_client::lift::LiftClientUpdateHandler;
use crate::core::traits::client::{ContainsClient, HasClientTypes};
use crate::core::traits::handlers::update_client::{AnyUpdateClientHandler, UpdateClientHandler};
use crate::core::traits::stores::client_reader::HasAnyClientReader;

pub struct CombineClientUpdateHandler<Handler, NextHandlers>(
    pub PhantomData<(Handler, NextHandlers)>,
);

impl<Context, Handler, NextHandlers, Client> AnyUpdateClientHandler<Context>
    for CombineClientUpdateHandler<Handler, NextHandlers>
where
    Context: HasAnyClientReader,
    Context: ContainsClient<Client>,
    Client: HasClientTypes,
    Handler: UpdateClientHandler<Context, Client = Client>,
    NextHandlers: AnyUpdateClientHandler<Context>,
    LiftClientUpdateHandler<Handler>: AnyUpdateClientHandler<Context>,
{
    fn check_client_header_and_update_state(
        context: &Context,
        client_id: &Context::ClientId,
        client_state: &Context::AnyClientState,
        new_client_header: &Context::AnyClientHeader,
    ) -> Result<(Context::AnyClientState, Context::AnyConsensusState), Context::Error> {
        let client_type = context.get_client_type(client_id)?;

        if client_type == Context::CLIENT_TYPE {
            <LiftClientUpdateHandler<Handler>>::check_client_header_and_update_state(
                context,
                client_id,
                client_state,
                new_client_header,
            )
        } else {
            NextHandlers::check_client_header_and_update_state(
                context,
                client_id,
                client_state,
                new_client_header,
            )
        }
    }
}
