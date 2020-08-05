use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics02_client::client::{ClientDef, ClientState};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::{Error, Kind};
use crate::ics02_client::handler::{ClientContext, ClientEvent, ClientKeeper};
use crate::ics02_client::msgs::MsgCreateClient;
use crate::ics24_host::identifier::ClientId;

pub struct CreateClientResult<CD: ClientDef> {
    client_id: ClientId,
    client_type: ClientType,
    client_state: CD::ClientState,
}

pub fn process<CD>(
    ctx: &dyn ClientContext<CD>,
    msg: MsgCreateClient<CD>,
) -> HandlerResult<CreateClientResult<CD>, Error>
where
    CD: ClientDef,
{
    let mut output = HandlerOutput::builder();

    let MsgCreateClient {
        client_id,
        client_type,
        consensus_state,
    } = msg;

    if ctx.client_state(&client_id).is_some() {
        return Err(Kind::ClientAlreadyExists(client_id).into());
    }

    output.log("success: no client state found");

    if ctx.client_type(&client_id).is_some() {
        return Err(Kind::ClientAlreadyExists(client_id).into());
    }

    output.log("success: no client type found");

    let client_state = CD::ClientState::from_consensus_state(consensus_state);

    output.emit(ClientEvent::ClientCreated(client_id.clone()));

    Ok(output.with_result(CreateClientResult {
        client_id,
        client_type,
        client_state,
    }))
}

pub fn keep<CD>(
    keeper: &mut dyn ClientKeeper<CD>,
    result: CreateClientResult<CD>,
) -> Result<(), Error>
where
    CD: ClientDef,
{
    keeper.store_client_state(result.client_id.clone(), result.client_state)?;
    keeper.store_client_type(result.client_id, result.client_type)?;

    Ok(())
}

