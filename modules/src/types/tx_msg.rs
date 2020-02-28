// Transactions messages must implement Msg trait

type  AccAddress = [byte];
trait Msg {
    fn Type(&self) -> &'static str;
    fn ValidateBasic(&self) -> error=;
    fn GetSignBytes(&self) -> &'static [byte];
    fn GetSigners(&self) -> &'static [AccAddress];
}
