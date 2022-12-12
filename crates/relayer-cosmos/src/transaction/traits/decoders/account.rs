use ibc_proto::cosmos::auth::v1beta1::BaseAccount;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_framework::base::core::traits::error::HasErrorType;

pub trait CanDecodeAccount: HasErrorType {
    fn decode_account(&self, raw_account: Any) -> Result<BaseAccount, Self::Error>;
}

pub trait AccountDecoder<Context>
where
    Context: HasErrorType,
{
    fn decode_account(context: &Context, raw_account: Any) -> Result<BaseAccount, Context::Error>;
}
