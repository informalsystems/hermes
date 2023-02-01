use core::marker::PhantomData;

use crate::core::traits::client::{
    ContainsClient, HasAnyClientMethods, HasClientTypes, InjectClientTypeMismatchError,
};
use crate::core::traits::error::HasError;
use crate::core::traits::handlers::update_client::{AnyUpdateClientHandler, UpdateClientHandler};
use crate::core::traits::ibc::HasIbcTypes;

pub struct LiftClientUpdateHandler<Handler>(pub PhantomData<Handler>);

impl<Context, Handler, Client> AnyUpdateClientHandler<Context> for LiftClientUpdateHandler<Handler>
where
    Context: HasError + HasIbcTypes + HasAnyClientMethods,
    Context: ContainsClient<Client>,
    Client: HasClientTypes,
    Handler: UpdateClientHandler<Context, Client = Client>,
    Context: InjectClientTypeMismatchError,
{
    fn check_client_header_and_update_state(
        context: &Context,
        client_id: &Context::ClientId,
        client_state: &Context::AnyClientState,
        new_client_header: &Context::AnyClientHeader,
    ) -> Result<(Context::AnyClientState, Context::AnyConsensusState), Context::Error> {
        let client_type = Context::client_state_type(client_state);

        if client_type != Context::CLIENT_TYPE {}

        let client_state = Context::try_from_any_client_state_ref(client_state)?;

        let client_header = Context::try_from_any_client_header_ref(new_client_header)?;

        let (new_client_state, new_consensus_state) =
            Handler::check_client_header_and_update_state(
                context,
                client_id,
                client_state,
                client_header,
            )?;

        Ok((
            Context::into_any_client_state(new_client_state),
            Context::into_any_consensus_state(new_consensus_state),
        ))
    }
}
