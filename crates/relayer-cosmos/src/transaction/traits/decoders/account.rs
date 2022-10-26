use ibc_proto::cosmos::auth::v1beta1::BaseAccount;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_framework::base::core::traits::error::HasError;

pub trait CanDecodeAccount: HasError {
    fn decode_account(&self, raw_account: Any) -> Result<BaseAccount, Self::Error>;
}

pub trait AccountDecoder<Context>
where
    Context: HasError,
{
    fn decode_account(context: &Context, raw_account: Any) -> Result<BaseAccount, Context::Error>;
}
