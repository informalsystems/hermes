pub mod ics20_fungible_token_transfer;

// TODO: These consts should move into the ICS27 namespace
pub const ICS27_BANK_SEND_TYPE_URL: &str = "/cosmos.bank.v1beta1.MsgSend";
pub const ICS27_SEND_TYPE_URL: &str = "/intertx.MsgSend";
pub const ICS27_REGISTER_TYPE_URL: &str = "/intertx.MsgRegister";
