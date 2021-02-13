use super::context::ICS20Context;
use super::error::Error;
use super::msgs::transfer::MsgTransfer;

pub fn sendTransfer<Ctx>(ctx: &Ctx, msg: MsgTransfer) -> Result<(), Error>
where
    Ctx: ICS20Context,
{
    Ok(())
}
