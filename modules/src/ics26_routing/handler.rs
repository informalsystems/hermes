use crate::context::LocalChainContext;
use crate::ics02_client::handler::dispatch as ics2_msg_dispatcher;
// use crate::ics03_connection::handler::dispatch as ics3_msg_dispatcher;
use crate::ics26_routing::error::{Error, Kind};
use crate::ics26_routing::msgs::ICS26RoutedMsgs;
use crate::ics26_routing::msgs::ICS26RoutedMsgs::{ICS2Msg, ICS3Msg};

/// Top-level dispatch function. Routes incoming ICS messages to their corresponding module.
pub fn dispatch<Ctx>(ctx: &mut Ctx, msg: ICS26RoutedMsgs) -> Result<(), Error>
where
    Ctx: LocalChainContext,
{
    // TODO: add dispatchers for ICS4 and others.
    match msg {
        ICS2Msg(msg) => {
            // TODO: Create the context for handling an ICS2 type of message (currently a mock).
            let mut client_ctx = ctx.get_client_context();
            let _res = ics2_msg_dispatcher(&mut client_ctx, msg)
                .map_err(|e| Kind::HandlerRaisedError.context(e).into())?;
        },

        ICS3Msg(msg) => {
            // TODO: Create the context for handling an ICS2 type of message (currently a mock).
            // let mut connection_ctx = ctx.get_connection_context();
            // let _res = ics3_msg_dispatcher(&mut connection_ctx, msg)
            //     .map_err(|e| Kind::HandlerRaisedError.context(e).into())?;
            // let _res = ics3_msg_dispatcher(ctx, msg).map_err(|e| Kind::HandlerRaisedError.context(e).into())?;
            Ok(())
        }
    };

    Ok(())
}
