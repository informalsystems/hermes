use ibc_proto::cosmos::tx::v1beta1::{SimulateRequest, SimulateResponse, Tx};
use tonic::codegen::http::Uri;

use crate::error::Error;

pub async fn send_tx_simulate(tx: Tx, grpc_address: &Uri) -> Result<SimulateResponse, Error> {
    use ibc_proto::cosmos::tx::v1beta1::service_client::ServiceClient;

    // The `tx` field of `SimulateRequest` was deprecated in Cosmos SDK 0.43 in favor of `tx_bytes`.
    let mut tx_bytes = vec![];
    prost::Message::encode(&tx, &mut tx_bytes).unwrap(); // FIXME: Handle error here

    #[allow(deprecated)]
    let req = SimulateRequest {
        tx: Some(tx), // needed for simulation to go through with Cosmos SDK <  0.43
        tx_bytes,     // needed for simulation to go through with Cosmos SDk >= 0.43
    };

    let mut client = ServiceClient::connect(grpc_address.clone())
        .await
        .map_err(Error::grpc_transport)?;

    let request = tonic::Request::new(req);
    let response = client
        .simulate(request)
        .await
        .map_err(Error::grpc_status)?
        .into_inner();

    Ok(response)
}
