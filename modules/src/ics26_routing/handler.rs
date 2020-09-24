use crate::ics02_client::handler::dispatch as ics2_msg_dispatcher;
use crate::ics03_connection::handler::dispatch as ics3_msg_dispatcher;
use crate::ics26_routing::context::ICS26Context;
use crate::ics26_routing::error::{Error, Kind};
use crate::ics26_routing::msgs::ICS26RoutingMsg;
use crate::ics26_routing::msgs::ICS26RoutingMsg::{ICS2Msg, ICS3Msg};
use ibc_proto::cosmos::tx::v1beta1::Tx;

// TODO: Implement this (the tx type is probably wrong also). Rough sketch:
// 1. deserialize & validate each message in the tx
// 2. invoke dispatch(ctx, ms)
// 3. if all message in the tx pass through correctly, then apply the side-effects to the context
pub fn deliver_tx<Ctx>(_ctx: &mut Ctx, _tx: Tx) -> Result<(), Error>
where
    Ctx: ICS26Context,
{
    unimplemented!()
}

/// Top-level dispatch function. Routes incoming ICS messages to their corresponding module.
pub fn dispatch<Ctx>(ctx: &mut Ctx, msg: ICS26RoutingMsg) -> Result<(), Error>
where
    Ctx: ICS26Context,
{
    match msg {
        ICS2Msg(msg) => {
            let handler_output =
                ics2_msg_dispatcher(ctx, msg).map_err(|e| Kind::HandlerRaisedError.context(e))?;

            ctx.store_client_result(handler_output.result)
                .map_err(|e| Kind::KeeperRaisedError.context(e))?;
        }

        ICS3Msg(msg) => {
            let handler_output =
                ics3_msg_dispatcher(ctx, msg).map_err(|e| Kind::HandlerRaisedError.context(e))?;

            ctx.store_connection_result(handler_output.result)
                .map_err(|e| Kind::KeeperRaisedError.context(e))?;
        } // TODO: add dispatchers for ICS4 and others.
    };

    Ok(())
}

// #[cfg(test)]
// mod tests {
//
//     #[test]
//     fn routing_dispatch() {
//         struct DispatchParams {
//             // ctx:
//         }
//     }
// }
