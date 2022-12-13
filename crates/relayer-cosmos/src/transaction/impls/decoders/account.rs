use ibc_proto::cosmos::auth::v1beta1::{BaseAccount, EthAccount};
use ibc_proto::google::protobuf::Any;
use ibc_relayer_framework::base::core::traits::error::HasErrorType;
use prost::{DecodeError, Message};

use crate::transaction::traits::decoders::account::AccountDecoder;

pub struct DecodeCosmosOrEthAccount;

pub trait InjectDecodeCosmosOrEthAccountError: HasErrorType {
    fn unknown_account_type_error(type_url: &str) -> Self::Error;

    fn empty_base_account_error() -> Self::Error;

    fn decode_cosmos_account_error(e: DecodeError) -> Self::Error;

    fn decode_eth_account_error(e: DecodeError) -> Self::Error;
}

impl<Context> AccountDecoder<Context> for DecodeCosmosOrEthAccount
where
    Context: InjectDecodeCosmosOrEthAccountError,
{
    fn decode_account(_: &Context, raw_account: Any) -> Result<BaseAccount, Context::Error> {
        if raw_account.type_url == "/cosmos.auth.v1beta1.BaseAccount" {
            let account = BaseAccount::decode(raw_account.value.as_slice())
                .map_err(Context::decode_cosmos_account_error)?;

            Ok(account)
        } else if raw_account.type_url.ends_with(".EthAccount") {
            Ok(EthAccount::decode(raw_account.value.as_slice())
                .map_err(Context::decode_eth_account_error)?
                .base_account
                .ok_or_else(Context::empty_base_account_error)?)
        } else {
            Err(Context::unknown_account_type_error(&raw_account.type_url))
        }
    }
}
