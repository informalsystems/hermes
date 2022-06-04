use core::str::FromStr;
use http::uri::Uri;
use ibc::applications::ics29_fee::packet_fee::IdentifiedPacketFees;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc::signer::Signer;
use ibc_proto::ibc::applications::fee::v1::query_client::QueryClient;
use ibc_proto::ibc::applications::fee::v1::{
    QueryCounterpartyAddressRequest, QueryIncentivizedPacketsForChannelRequest,
};
use tonic::Code;

use crate::error::Error;

pub async fn query_counterparty_address(
    grpc_address: &Uri,
    channel_id: &ChannelId,
    address: &Signer,
) -> Result<Option<Signer>, Error> {
    let mut client = QueryClient::connect(grpc_address.clone())
        .await
        .map_err(Error::grpc_transport)?;

    let request = QueryCounterpartyAddressRequest {
        channel_id: channel_id.to_string(),
        relayer_address: address.to_string(),
    };

    let result = client.counterparty_address(request).await;

    match result {
        Ok(response) => {
            let counterparty_address =
                Signer::from_str(&response.into_inner().counterparty_address).unwrap();

            Ok(Some(counterparty_address))
        }
        Err(e) => {
            if e.code() == Code::NotFound {
                Ok(None)
            } else {
                Err(Error::grpc_status(e))
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

    let request = QueryIncentivizedPacketsForChannelRequest {
        channel_id: channel_id.to_string(),
        port_id: port_id.to_string(),
        pagination: None,
        query_height: 0,
    };

    let response = client
        .incentivized_packets_for_channel(request)
        .await
        .map_err(Error::grpc_status)?;

    let raw_packets = response.into_inner().incentivized_packets;

    let packets = raw_packets
        .into_iter()
        .map(IdentifiedPacketFees::try_from)
        .collect::<Result<_, _>>()
        .map_err(Error::ics29)?;

    Ok(packets)
}
