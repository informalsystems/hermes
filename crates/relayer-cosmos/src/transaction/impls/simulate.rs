use async_trait::async_trait;
use ibc_proto::cosmos::tx::v1beta1::service_client::ServiceClient;
use ibc_proto::cosmos::tx::v1beta1::{SimulateRequest, SimulateResponse, Tx};
use ibc_relayer_framework::base::core::traits::error::{HasError, InjectError};
use prost::EncodeError;
use tonic::transport::Error as TransportError;
use tonic::Status as StatusError;

use crate::transaction::traits::fields::HasGrpcAddress;

#[async_trait]
pub trait CanSendTxSimulate: HasError {
    async fn send_tx_simulate(&self, tx: Tx) -> Result<SimulateResponse, Self::Error>;
}

#[async_trait]
impl<Context> CanSendTxSimulate for Context
where
    Context: InjectError<EncodeError>
        + InjectError<TransportError>
        + InjectError<StatusError>
        + HasGrpcAddress,
{
    async fn send_tx_simulate(&self, tx: Tx) -> Result<SimulateResponse, Self::Error> {
        let grpc_address = self.grpc_address();

        // The `tx` field of `SimulateRequest` was deprecated in Cosmos SDK 0.43 in favor of `tx_bytes`.
        let mut tx_bytes = vec![];
        prost::Message::encode(&tx, &mut tx_bytes).map_err(Context::inject_error)?;

        #[allow(deprecated)]
        let req = SimulateRequest {
            tx: Some(tx), // needed for simulation to go through with Cosmos SDK <  0.43
            tx_bytes,     // needed for simulation to go through with Cosmos SDk >= 0.43
        };

        let mut client = ServiceClient::connect(grpc_address.clone())
            .await
            .map_err(Context::inject_error)?;

        let request = tonic::Request::new(req);
        let response = client
            .simulate(request)
            .await
            .map_err(Context::inject_error)?
            .into_inner();

        Ok(response)
    }
}
