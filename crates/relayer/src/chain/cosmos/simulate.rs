use ibc_proto::cosmos::tx::v1beta1::{
    service_client::ServiceClient,
    SimulateRequest,
    SimulateResponse,
    Tx,
};
use tonic::codegen::http::Uri;

use crate::{
    config::default::max_grpc_decoding_size,
    error::Error,
};

pub async fn send_tx_simulate(grpc_address: &Uri, tx: Tx) -> Result<SimulateResponse, Error> {
    let mut tx_bytes = vec![];
    prost::Message::encode(&tx, &mut tx_bytes)
        .map_err(|e| Error::protobuf_encode(String::from("Transaction"), e))?;

    let req = SimulateRequest {
        tx_bytes,
        ..Default::default()
    };

    let mut client = ServiceClient::connect(grpc_address.clone())
        .await
        .map_err(Error::grpc_transport)?;

    client = client.max_decoding_message_size(max_grpc_decoding_size().get_bytes() as usize);

    let request = tonic::Request::new(req);
    let response = client
        .simulate(request)
        .await
        .map_err(|e| Error::grpc_status(e, "send_tx_simulate".to_owned()))?
        .into_inner();

    Ok(response)
}
