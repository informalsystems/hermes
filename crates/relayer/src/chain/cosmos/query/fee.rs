use http::uri::Uri;
use ibc_proto::ibc::{
    applications::fee::v1::{
        query_client::QueryClient,
        QueryCounterpartyPayeeRequest,
        QueryIncentivizedPacketsForChannelRequest,
    },
    apps::fee::v1::{
        QueryIncentivizedPacketRequest,
        QueryIncentivizedPacketResponse,
    },
};
use ibc_relayer_types::{
    applications::ics29_fee::packet_fee::IdentifiedPacketFees,
    core::ics24_host::identifier::{
        ChannelId,
        PortId,
    },
    signer::Signer,
};
use tonic::Code;

use crate::{
    config::default::max_grpc_decoding_size,
    error::Error,
};

pub async fn query_counterparty_payee(
    grpc_address: &Uri,
    channel_id: &ChannelId,
    address: &Signer,
) -> Result<Option<String>, Error> {
    let mut client = QueryClient::connect(grpc_address.clone())
        .await
        .map_err(Error::grpc_transport)?;

    client = client.max_decoding_message_size(max_grpc_decoding_size().get_bytes() as usize);

    let request = QueryCounterpartyPayeeRequest {
        channel_id: channel_id.to_string(),
        relayer: address.to_string(),
    };

    let result = client.counterparty_payee(request).await;

    match result {
        Ok(response) => {
            let counterparty_payee = response.into_inner().counterparty_payee;

            Ok(Some(counterparty_payee))
        }
        Err(e) => {
            if e.code() == Code::NotFound {
                Ok(None)
            } else {
                Err(Error::grpc_status(e, "query_counterparty_payee".to_owned()))
            }
        }
    }
}

pub async fn query_incentivized_packets(
    grpc_address: &Uri,
    channel_id: &ChannelId,
    port_id: &PortId,
) -> Result<Vec<IdentifiedPacketFees>, Error> {
    let mut client = QueryClient::connect(grpc_address.clone())
        .await
        .map_err(Error::grpc_transport)?;

    client = client.max_decoding_message_size(max_grpc_decoding_size().get_bytes() as usize);

    let request = QueryIncentivizedPacketsForChannelRequest {
        channel_id: channel_id.to_string(),
        port_id: port_id.to_string(),
        pagination: None,
        query_height: 0,
    };

    let response = client
        .incentivized_packets_for_channel(request)
        .await
        .map_err(|e| Error::grpc_status(e, "query_incentivized_packets".to_owned()))?;

    let raw_packets = response.into_inner().incentivized_packets;

    let packets = raw_packets
        .into_iter()
        .map(IdentifiedPacketFees::try_from)
        .collect::<Result<_, _>>()
        .map_err(Error::ics29)?;

    Ok(packets)
}

/// Query the incentivized packet for a specific packet at a specific height.
pub async fn query_incentivized_packet(
    grpc_address: &Uri,
    request: QueryIncentivizedPacketRequest,
) -> Result<QueryIncentivizedPacketResponse, Error> {
    let mut client = QueryClient::connect(grpc_address.clone())
        .await
        .map_err(Error::grpc_transport)?;

    client = client.max_decoding_message_size(max_grpc_decoding_size().get_bytes() as usize);

    let response = client
        .incentivized_packet(tonic::Request::new(request))
        .await
        .map_err(|e| Error::grpc_status(e, "query_incentivized_packet".to_owned()))?;

    Ok(response.into_inner())
}
