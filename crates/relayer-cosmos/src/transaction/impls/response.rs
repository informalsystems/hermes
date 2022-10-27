use ibc_relayer_framework::base::core::traits::error::HasError;
use tendermint::abci::Code;

pub trait InjectRpcResponseError: HasError {
    fn rpc_response_error(code: Code) -> Self::Error;
}

pub trait CanValidateRpcResponse: HasError {
    fn validate_rpc_response_code(code: Code) -> Result<(), Self::Error>;
}

impl<Context> CanValidateRpcResponse for Context
where
    Context: InjectRpcResponseError,
{
    fn validate_rpc_response_code(code: Code) -> Result<(), Self::Error> {
        if code.is_err() {
            Err(Context::rpc_response_error(code))
        } else {
            Ok(())
        }
    }
}
