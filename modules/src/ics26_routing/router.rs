use crate::handler::HandlerOutput;
use crate::ics02_client::context::{ClientKeeper, ClientReader};
use crate::ics02_client::handler::dispatch as ics2_msg_dispatcher;
use crate::ics03_connection::handler::dispatch as ics3_msg_dispatcher;
use crate::ics26_routing::msgs::ICS26RoutedMsgs;
use crate::ics26_routing::msgs::ICS26RoutedMsgs::{ICS2Msg, ICS3Msg};
use crate::ics26_routing::error::{Kind, Error};

pub fn route<Ctx>(ctx: &mut Ctx, msg: ICS26RoutedMsgs) -> Result<HandlerOutput<()>, Error>
where
    Ctx: ClientReader + ClientKeeper,
{
    match msg {
        ICS2Msg(msg) => ics2_msg_dispatcher(ctx, msg).map_err(|e| Kind::HandlerRaisedError.context(e).into())?,
        ICS3Msg(msg) => ics3_msg_dispatcher(ctx, msg).map_err(|e| Kind::HandlerRaisedError.context(e).into())?,
    }
}
