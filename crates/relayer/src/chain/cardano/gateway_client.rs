//! gRPC client for Cardano Gateway
//!
//! This module provides a client for interacting with the Cardano Gateway service,
//! which handles Cardano blockchain queries, transaction building, and submission.

use super::error::Error;
use super::generated::ibc::cardano::v1::{
    cardano_msg_client::CardanoMsgClient, SubmitSignedTxRequest, SubmitSignedTxResponse,
};
use super::generated::ibc::core::channel::v1::msg_client::MsgClient as GenChannelMsgClient;
use super::generated::ibc::core::client::v1::msg_client::MsgClient as GenClientMsgClient;
use super::generated::ibc::core::connection::v1::msg_client::MsgClient as GenConnectionMsgClient;
use ibc_proto::google::protobuf::Any as ProtoAny;
use ibc_proto::ibc::core::channel::v1::query_client::QueryClient as ChannelQueryClient;
use ibc_proto::ibc::core::channel::v1::{
    QueryChannelClientStateRequest, QueryChannelClientStateResponse, QueryChannelRequest,
    QueryChannelsRequest, QueryConnectionChannelsRequest, QueryNextSequenceReceiveRequest,
    QueryPacketAcknowledgementRequest, QueryPacketAcknowledgementsRequest,
    QueryPacketCommitmentRequest, QueryPacketCommitmentsRequest, QueryPacketReceiptRequest,
    QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};
use ibc_proto::ibc::core::client::v1::query_client::QueryClient as ClientQueryClient;
use ibc_proto::ibc::core::client::v1::{
    QueryClientStateRequest, QueryClientStateResponse, QueryClientStatesRequest,
    QueryConsensusStateHeightsRequest, QueryConsensusStateHeightsResponse,
    QueryConsensusStateRequest, QueryConsensusStateResponse, QueryConsensusStatesRequest,
    QueryConsensusStatesResponse,
};
use ibc_proto::ibc::core::connection::v1::query_client::QueryClient as ConnectionQueryClient;
use ibc_proto::ibc::core::connection::v1::{
    QueryClientConnectionsRequest, QueryConnectionRequest, QueryConnectionsRequest,
};
use ibc_relayer_types::clients::ics08_cardano::header::Header as MithrilHeader;
use ibc_relayer_types::Height;
use tonic::transport::Channel;

/// Unsigned transaction response from Gateway
#[derive(Debug, Clone)]
pub struct UnsignedTx {
    pub cbor_hex: String,
    pub description: String,
}

/// Transaction submission response from Gateway
#[derive(Debug, Clone)]
pub struct TxSubmitResponse {
    pub tx_hash: String,
    pub height: Option<Height>,
    pub events: Vec<IbcEvent>,
}

/// Simplified IBC event structure for Gateway responses
#[derive(Debug, Clone)]
pub struct IbcEvent {
    pub event_type: String,
    pub attributes: Vec<(String, String)>,
}

/// Client for communicating with Cardano Gateway
#[derive(Clone)]
pub struct GatewayClient {
    endpoint: String,
    channel: Channel,
}

impl GatewayClient {
    /// Create a new Gateway client and establish a gRPC connection
    pub async fn new(endpoint: String) -> Result<Self, Error> {
        tracing::info!("Connecting to Cardano Gateway at {}", endpoint);

        let channel = Channel::from_shared(endpoint.clone())
            .map_err(|e| Error::GatewayClient(e.to_string()))?
            .connect()
            .await?;

        Ok(Self { endpoint, channel })
    }

    /// Query the latest block height from the Gateway
    pub async fn query_latest_height(&self) -> Result<Height, Error> {
        use super::generated::ibc::core::client::v1::{
            query_client::QueryClient, QueryLatestHeightRequest,
        };

        let mut client = QueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryLatestHeightRequest {});

        let response = client.latest_height(request).await?.into_inner();

        tracing::debug!("Queried latest height: {}", response.height);

        // Height format: revision_number-revision_height
        // For Cardano, we use revision_number = 0
        Height::new(0, response.height)
            .map_err(|e| Error::Query(format!("Invalid height {}: {}", response.height, e)))
    }

    /// Query the canonical Mithril client state/consensus state for creating a new client.
    pub async fn query_new_client(
        &self,
        height: u64,
    ) -> Result<super::generated::ibc::core::client::v1::QueryNewClientResponse, Error> {
        use super::generated::ibc::core::client::v1::{
            query_client::QueryClient, QueryNewClientRequest,
        };

        let mut client = QueryClient::new(self.channel.clone());
        let request = tonic::Request::new(QueryNewClientRequest { height });
        let response = client.new_client(request).await?.into_inner();

        Ok(response)
    }

    /// Query client state for a specific client ID
    pub async fn query_client_state(
        &self,
        client_id: &str,
    ) -> Result<QueryClientStateResponse, Error> {
        let mut client = ClientQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryClientStateRequest {
            client_id: client_id.to_string(),
        });

        let response = client.client_state(request).await?.into_inner();

        Ok(response)
    }

    /// Query consensus state for a specific client ID and height
    pub async fn query_consensus_state(
        &self,
        client_id: &str,
        height: Height,
    ) -> Result<QueryConsensusStateResponse, Error> {
        let mut client = ClientQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryConsensusStateRequest {
            client_id: client_id.to_string(),
            revision_number: height.revision_number(),
            revision_height: height.revision_height(),
            latest_height: false,
        });

        let response = client.consensus_state(request).await?.into_inner();

        Ok(response)
    }

    /// Query consensus state heights for a specific client ID.
    pub async fn query_consensus_state_heights(
        &self,
        request: QueryConsensusStateHeightsRequest,
    ) -> Result<QueryConsensusStateHeightsResponse, Error> {
        let mut client = ClientQueryClient::new(self.channel.clone());
        let request = tonic::Request::new(request);
        let response = client.consensus_state_heights(request).await?.into_inner();
        Ok(response)
    }

    /// Query all consensus states for a specific client ID.
    pub async fn query_consensus_states(
        &self,
        request: QueryConsensusStatesRequest,
    ) -> Result<QueryConsensusStatesResponse, Error> {
        let mut client = ClientQueryClient::new(self.channel.clone());
        let request = tonic::Request::new(request);
        let response = client.consensus_states(request).await?.into_inner();
        Ok(response)
    }

    /// Query header at a specific height
    ///
    /// This is required for building headers used in `MsgUpdateClient`.
    pub async fn query_header(&self, height: Height) -> Result<MithrilHeader, Error> {
        use super::generated::ibc::core::types::v1::query_client::QueryClient as TypesQueryClient;
        use super::generated::ibc::core::types::v1::QueryIbcHeaderRequest;

        let mut client = TypesQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryIbcHeaderRequest {
            height: height.revision_height(),
        });

        let response = client.ibc_header(request).await?.into_inner();

        let header_any = response
            .header
            .ok_or_else(|| Error::Query("No header in response".to_string()))?;

        let header_any = ProtoAny {
            type_url: header_any.type_url,
            value: header_any.value,
        };

        header_any
            .try_into()
            .map_err(|e: ibc_relayer_types::core::ics02_client::error::Error| {
                Error::Ibc(e.to_string())
            })
    }

    /// Query block results at a specific height.
    pub async fn query_block_results(
        &self,
        height: u64,
    ) -> Result<super::generated::ibc::core::types::v1::QueryBlockResultsResponse, Error> {
        use super::generated::ibc::core::types::v1::query_client::QueryClient as TypesQueryClient;
        use super::generated::ibc::core::types::v1::QueryBlockResultsRequest;

        let mut client = TypesQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryBlockResultsRequest { height });
        let response = client.block_results(request).await?.into_inner();

        Ok(response)
    }

    /// Search for blocks containing packet-related events.
    pub async fn query_block_search(
        &self,
        packet_src_channel: String,
        packet_dst_channel: String,
        packet_sequence: String,
        limit: u64,
    ) -> Result<super::generated::ibc::core::types::v1::QueryBlockSearchResponse, Error> {
        self.query_block_search_page(
            packet_src_channel,
            packet_dst_channel,
            packet_sequence,
            limit,
            1,
        )
        .await
    }

    /// Search for blocks containing packet-related events, returning all pages.
    pub async fn query_block_search_all(
        &self,
        packet_src_channel: String,
        packet_dst_channel: String,
        packet_sequence: String,
        limit: u64,
    ) -> Result<super::generated::ibc::core::types::v1::QueryBlockSearchResponse, Error> {
        let mut page = 1u64;
        let mut blocks = Vec::new();
        let mut total_count = None;

        loop {
            let response = self
                .query_block_search_page(
                    packet_src_channel.clone(),
                    packet_dst_channel.clone(),
                    packet_sequence.clone(),
                    limit,
                    page,
                )
                .await?;

            if total_count.is_none() {
                total_count = Some(response.total_count);
            }

            let page_is_empty = response.blocks.is_empty();
            blocks.extend(response.blocks);

            let total = total_count.unwrap_or(0);
            if total == 0 || blocks.len() as u64 >= total {
                break;
            }

            // Defensive: avoid infinite pagination if server returns empty pages.
            if page > 1 && page_is_empty {
                break;
            }

            page = page.saturating_add(1);
        }

        Ok(
            super::generated::ibc::core::types::v1::QueryBlockSearchResponse {
                total_count: total_count.unwrap_or(blocks.len() as u64),
                blocks,
            },
        )
    }

    async fn query_block_search_page(
        &self,
        packet_src_channel: String,
        packet_dst_channel: String,
        packet_sequence: String,
        limit: u64,
        page: u64,
    ) -> Result<super::generated::ibc::core::types::v1::QueryBlockSearchResponse, Error> {
        use super::generated::ibc::core::types::v1::query_client::QueryClient as TypesQueryClient;
        use super::generated::ibc::core::types::v1::QueryBlockSearchRequest;

        let mut client = TypesQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryBlockSearchRequest {
            packet_src_channel,
            packet_dst_channel,
            packet_sequence,
            limit,
            page,
        });

        let response = client.block_search(request).await?.into_inner();
        Ok(response)
    }

    /// Query a transaction by hash.
    pub async fn query_transaction_by_hash(
        &self,
        hash: String,
    ) -> Result<super::generated::ibc::core::types::v1::QueryTransactionByHashResponse, Error> {
        use super::generated::ibc::core::types::v1::query_client::QueryClient as TypesQueryClient;
        use super::generated::ibc::core::types::v1::QueryTransactionByHashRequest;

        let mut client = TypesQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryTransactionByHashRequest { hash });
        let response = client.transaction_by_hash(request).await?.into_inner();
        Ok(response)
    }

    /// Query the client state associated with a channel.
    pub async fn query_channel_client_state(
        &self,
        port_id: &str,
        channel_id: &str,
    ) -> Result<Vec<u8>, Error> {
        let mut client = ChannelQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryChannelClientStateRequest {
            port_id: port_id.to_string(),
            channel_id: channel_id.to_string(),
        });

        let response: QueryChannelClientStateResponse =
            client.channel_client_state(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query connection state
    pub async fn query_connection(&self, connection_id: &str) -> Result<Vec<u8>, Error> {
        let mut client = ConnectionQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryConnectionRequest {
            connection_id: connection_id.to_string(),
        });

        let response = client.connection(request).await?.into_inner();

        // Return serialized connection
        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query all connections
    pub async fn query_connections(&self) -> Result<Vec<u8>, Error> {
        let mut client = ConnectionQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryConnectionsRequest { pagination: None });

        let response = client.connections(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query channel state
    pub async fn query_channel(&self, port_id: &str, channel_id: &str) -> Result<Vec<u8>, Error> {
        let mut client = ChannelQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryChannelRequest {
            port_id: port_id.to_string(),
            channel_id: channel_id.to_string(),
        });

        let response = client.channel(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query all channels
    pub async fn query_channels(&self) -> Result<Vec<u8>, Error> {
        let mut client = ChannelQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryChannelsRequest { pagination: None });

        let response = client.channels(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query all clients
    pub async fn query_clients(&self) -> Result<Vec<u8>, Error> {
        let mut client = ClientQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryClientStatesRequest { pagination: None });

        let response = client.client_states(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query connections associated with a client
    pub async fn query_client_connections(&self, client_id: &str) -> Result<Vec<u8>, Error> {
        let mut client = ConnectionQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryClientConnectionsRequest {
            client_id: client_id.to_string(),
        });

        let response = client.client_connections(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query channels associated with a connection
    pub async fn query_connection_channels(&self, connection_id: &str) -> Result<Vec<u8>, Error> {
        let mut client = ChannelQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryConnectionChannelsRequest {
            connection: connection_id.to_string(),
            pagination: None,
        });

        let response = client.connection_channels(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query packet commitment
    pub async fn query_packet_commitment(
        &self,
        port_id: &str,
        channel_id: &str,
        sequence: u64,
    ) -> Result<Vec<u8>, Error> {
        let mut client = ChannelQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryPacketCommitmentRequest {
            port_id: port_id.to_string(),
            channel_id: channel_id.to_string(),
            sequence,
        });

        let response = client.packet_commitment(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query all packet commitments for a channel
    pub async fn query_packet_commitments(
        &self,
        port_id: &str,
        channel_id: &str,
    ) -> Result<Vec<u8>, Error> {
        let mut client = ChannelQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryPacketCommitmentsRequest {
            port_id: port_id.to_string(),
            channel_id: channel_id.to_string(),
            pagination: None,
        });

        let response = client.packet_commitments(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query packet receipt
    pub async fn query_packet_receipt(
        &self,
        port_id: &str,
        channel_id: &str,
        sequence: u64,
    ) -> Result<Vec<u8>, Error> {
        let mut client = ChannelQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryPacketReceiptRequest {
            port_id: port_id.to_string(),
            channel_id: channel_id.to_string(),
            sequence,
        });

        let response = client.packet_receipt(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query packet acknowledgement
    pub async fn query_packet_acknowledgement(
        &self,
        port_id: &str,
        channel_id: &str,
        sequence: u64,
    ) -> Result<Vec<u8>, Error> {
        let mut client = ChannelQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryPacketAcknowledgementRequest {
            port_id: port_id.to_string(),
            channel_id: channel_id.to_string(),
            sequence,
        });

        let response = client.packet_acknowledgement(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query all packet acknowledgements for a channel
    pub async fn query_packet_acknowledgements(
        &self,
        port_id: &str,
        channel_id: &str,
    ) -> Result<Vec<u8>, Error> {
        let mut client = ChannelQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryPacketAcknowledgementsRequest {
            port_id: port_id.to_string(),
            channel_id: channel_id.to_string(),
            pagination: None,
            packet_commitment_sequences: vec![],
        });

        let response = client.packet_acknowledgements(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query unreceived packets
    pub async fn query_unreceived_packets(
        &self,
        port_id: &str,
        channel_id: &str,
        sequences: Vec<u64>,
    ) -> Result<Vec<u8>, Error> {
        let mut client = ChannelQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryUnreceivedPacketsRequest {
            port_id: port_id.to_string(),
            channel_id: channel_id.to_string(),
            packet_commitment_sequences: sequences,
        });

        let response = client.unreceived_packets(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query unreceived acknowledgements
    pub async fn query_unreceived_acknowledgements(
        &self,
        port_id: &str,
        channel_id: &str,
        sequences: Vec<u64>,
    ) -> Result<Vec<u8>, Error> {
        let mut client = ChannelQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryUnreceivedAcksRequest {
            port_id: port_id.to_string(),
            channel_id: channel_id.to_string(),
            packet_ack_sequences: sequences,
        });

        let response = client.unreceived_acks(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Query next sequence receive for a channel
    pub async fn query_next_sequence_receive(
        &self,
        port_id: &str,
        channel_id: &str,
    ) -> Result<Vec<u8>, Error> {
        let mut client = ChannelQueryClient::new(self.channel.clone());

        let request = tonic::Request::new(QueryNextSequenceReceiveRequest {
            port_id: port_id.to_string(),
            channel_id: channel_id.to_string(),
        });

        let response = client.next_sequence_receive(request).await?.into_inner();

        Ok(prost::Message::encode_to_vec(&response))
    }

    /// Build unsigned transaction for IBC message via Gateway
    /// Gateway returns CBOR hex that Hermes will sign
    ///
    /// This method routes IBC messages to the appropriate Gateway Msg service based on the type_url.
    /// The type_url format is: "/ibc.core.{module}.v1.Msg{Operation}"
    pub async fn build_ibc_tx(
        &self,
        type_url: &str,
        message_data: Vec<u8>,
    ) -> Result<UnsignedTx, Error> {
        tracing::info!(
            "Building unsigned transaction for message type: {}",
            type_url
        );

        // Route based on type_url
        match type_url {
            // IBC Client messages
            "/ibc.core.client.v1.MsgCreateClient" => {
                self.build_create_client_tx(message_data).await
            }
            "/ibc.core.client.v1.MsgUpdateClient" => {
                self.build_update_client_tx(message_data).await
            }

            // IBC Connection messages
            "/ibc.core.connection.v1.MsgConnectionOpenInit" => {
                self.build_connection_open_init_tx(message_data).await
            }
            "/ibc.core.connection.v1.MsgConnectionOpenTry" => {
                self.build_connection_open_try_tx(message_data).await
            }
            "/ibc.core.connection.v1.MsgConnectionOpenAck" => {
                self.build_connection_open_ack_tx(message_data).await
            }
            "/ibc.core.connection.v1.MsgConnectionOpenConfirm" => {
                self.build_connection_open_confirm_tx(message_data).await
            }

            // IBC Channel messages
            "/ibc.core.channel.v1.MsgChannelOpenInit" => {
                self.build_channel_open_init_tx(message_data).await
            }
            "/ibc.core.channel.v1.MsgChannelOpenTry" => {
                self.build_channel_open_try_tx(message_data).await
            }
            "/ibc.core.channel.v1.MsgChannelOpenAck" => {
                self.build_channel_open_ack_tx(message_data).await
            }
            "/ibc.core.channel.v1.MsgChannelOpenConfirm" => {
                self.build_channel_open_confirm_tx(message_data).await
            }
            "/ibc.core.channel.v1.MsgChannelCloseInit" => {
                self.build_channel_close_init_tx(message_data).await
            }
            "/ibc.core.channel.v1.MsgChannelCloseConfirm" => {
                self.build_channel_close_confirm_tx(message_data).await
            }

            // IBC Packet messages
            "/ibc.core.channel.v1.MsgRecvPacket" => self.build_recv_packet_tx(message_data).await,
            "/ibc.core.channel.v1.MsgAcknowledgement" => {
                self.build_acknowledgement_tx(message_data).await
            }
            "/ibc.core.channel.v1.MsgTimeout" => self.build_timeout_tx(message_data).await,
            "/ibc.core.channel.v1.MsgTimeoutOnClose" => {
                self.build_timeout_on_close_tx(message_data).await
            }

            // IBC Transfer messages
            "/ibc.applications.transfer.v1.MsgTransfer" => {
                self.build_transfer_tx(message_data).await
            }

            // Unknown message type
            _ => {
                tracing::error!("Unsupported message type: {}", type_url);
                Err(Error::Transaction(format!(
                    "Unsupported message type: {}",
                    type_url
                )))
            }
        }
    }

    //
    // Helper methods for building each message type
    //

    async fn build_create_client_tx(&self, message_data: Vec<u8>) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::client::v1::MsgCreateClient;
        use prost::Message;

        let msg = MsgCreateClient::decode(&message_data[..])
            .map_err(|e| Error::Transaction(format!("Failed to decode MsgCreateClient: {}", e)))?;

        let mut client = GenClientMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.create_client(request).await?.into_inner();

        // Extract unsigned CBOR from response
        // Gateway returns unsigned_tx as google.protobuf.Any with CBOR hex in the value field
        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in CreateClient response".to_string())
        })?;

        // The value field contains the CBOR hex string
        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "CreateClient: received unsigned CBOR (length: {}), client_id: {}",
            cbor_hex.len(),
            response.client_id
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!("MsgCreateClient (client_id: {})", response.client_id),
        })
    }

    async fn build_update_client_tx(&self, message_data: Vec<u8>) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::client::v1::MsgUpdateClient;
        use prost::Message;

        let msg = MsgUpdateClient::decode(&message_data[..])
            .map_err(|e| Error::Transaction(format!("Failed to decode MsgUpdateClient: {}", e)))?;

        let client_id = msg.client_id.clone();

        let mut client = GenClientMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.update_client(request).await?.into_inner();

        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in UpdateClient response".to_string())
        })?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "UpdateClient: received unsigned CBOR (length: {}), client_id: {}",
            cbor_hex.len(),
            client_id
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!("MsgUpdateClient (client_id: {})", client_id),
        })
    }

    async fn build_connection_open_init_tx(
        &self,
        message_data: Vec<u8>,
    ) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::connection::v1::MsgConnectionOpenInit;
        use prost::Message;

        let msg = MsgConnectionOpenInit::decode(&message_data[..]).map_err(|e| {
            Error::Transaction(format!("Failed to decode MsgConnectionOpenInit: {}", e))
        })?;

        let client_id = msg.client_id.clone();

        let mut client = GenConnectionMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.connection_open_init(request).await?.into_inner();

        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in ConnectionOpenInit response".to_string())
        })?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "ConnectionOpenInit: received unsigned CBOR (length: {}), client_id: {}",
            cbor_hex.len(),
            client_id
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!("MsgConnectionOpenInit (client_id: {})", client_id),
        })
    }

    async fn build_connection_open_try_tx(
        &self,
        message_data: Vec<u8>,
    ) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::connection::v1::MsgConnectionOpenTry;
        use prost::Message;

        let msg = MsgConnectionOpenTry::decode(&message_data[..]).map_err(|e| {
            Error::Transaction(format!("Failed to decode MsgConnectionOpenTry: {}", e))
        })?;

        let client_id = msg.client_id.clone();

        let mut client = GenConnectionMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.connection_open_try(request).await?.into_inner();

        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in ConnectionOpenTry response".to_string())
        })?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "ConnectionOpenTry: received unsigned CBOR (length: {}), client_id: {}",
            cbor_hex.len(),
            client_id
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!("MsgConnectionOpenTry (client_id: {})", client_id),
        })
    }

    async fn build_connection_open_ack_tx(
        &self,
        message_data: Vec<u8>,
    ) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::connection::v1::MsgConnectionOpenAck;
        use prost::Message;

        let msg = MsgConnectionOpenAck::decode(&message_data[..]).map_err(|e| {
            Error::Transaction(format!("Failed to decode MsgConnectionOpenAck: {}", e))
        })?;

        let connection_id = msg.connection_id.clone();

        let mut client = GenConnectionMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.connection_open_ack(request).await?.into_inner();

        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in ConnectionOpenAck response".to_string())
        })?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "ConnectionOpenAck: received unsigned CBOR (length: {}), connection_id: {}",
            cbor_hex.len(),
            connection_id
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!("MsgConnectionOpenAck (connection_id: {})", connection_id),
        })
    }

    async fn build_connection_open_confirm_tx(
        &self,
        message_data: Vec<u8>,
    ) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::connection::v1::MsgConnectionOpenConfirm;
        use prost::Message;

        let msg = MsgConnectionOpenConfirm::decode(&message_data[..]).map_err(|e| {
            Error::Transaction(format!("Failed to decode MsgConnectionOpenConfirm: {}", e))
        })?;

        let connection_id = msg.connection_id.clone();

        let mut client = GenConnectionMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.connection_open_confirm(request).await?.into_inner();

        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in ConnectionOpenConfirm response".to_string())
        })?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "ConnectionOpenConfirm: received unsigned CBOR (length: {}), connection_id: {}",
            cbor_hex.len(),
            connection_id
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!(
                "MsgConnectionOpenConfirm (connection_id: {})",
                connection_id
            ),
        })
    }

    async fn build_channel_open_init_tx(&self, message_data: Vec<u8>) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::channel::v1::MsgChannelOpenInit;
        use prost::Message;

        let msg = MsgChannelOpenInit::decode(&message_data[..]).map_err(|e| {
            Error::Transaction(format!("Failed to decode MsgChannelOpenInit: {}", e))
        })?;

        let port_id = msg.port_id.clone();

        let mut client = GenChannelMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.channel_open_init(request).await?.into_inner();

        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in ChannelOpenInit response".to_string())
        })?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "ChannelOpenInit: received unsigned CBOR (length: {}), port_id: {}, channel_id: {}",
            cbor_hex.len(),
            port_id,
            response.channel_id
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!(
                "MsgChannelOpenInit (port: {}, channel: {})",
                port_id, response.channel_id
            ),
        })
    }

    async fn build_channel_open_try_tx(&self, message_data: Vec<u8>) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::channel::v1::MsgChannelOpenTry;
        use prost::Message;

        let msg = MsgChannelOpenTry::decode(&message_data[..]).map_err(|e| {
            Error::Transaction(format!("Failed to decode MsgChannelOpenTry: {}", e))
        })?;

        let port_id = msg.port_id.clone();

        let mut client = GenChannelMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.channel_open_try(request).await?.into_inner();

        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in ChannelOpenTry response".to_string())
        })?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "ChannelOpenTry: received unsigned CBOR (length: {}), port_id: {}",
            cbor_hex.len(),
            port_id
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!("MsgChannelOpenTry (port: {})", port_id),
        })
    }

    async fn build_channel_open_ack_tx(&self, message_data: Vec<u8>) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::channel::v1::MsgChannelOpenAck;
        use prost::Message;

        let msg = MsgChannelOpenAck::decode(&message_data[..]).map_err(|e| {
            Error::Transaction(format!("Failed to decode MsgChannelOpenAck: {}", e))
        })?;

        let port_id = msg.port_id.clone();
        let channel_id = msg.channel_id.clone();

        let mut client = GenChannelMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.channel_open_ack(request).await?.into_inner();

        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in ChannelOpenAck response".to_string())
        })?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "ChannelOpenAck: received unsigned CBOR (length: {}), port_id: {}, channel_id: {}",
            cbor_hex.len(),
            port_id,
            channel_id
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!(
                "MsgChannelOpenAck (port: {}, channel: {})",
                port_id, channel_id
            ),
        })
    }

    async fn build_channel_open_confirm_tx(
        &self,
        message_data: Vec<u8>,
    ) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::channel::v1::MsgChannelOpenConfirm;
        use prost::Message;

        let msg = MsgChannelOpenConfirm::decode(&message_data[..]).map_err(|e| {
            Error::Transaction(format!("Failed to decode MsgChannelOpenConfirm: {}", e))
        })?;

        let port_id = msg.port_id.clone();
        let channel_id = msg.channel_id.clone();

        let mut client = GenChannelMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.channel_open_confirm(request).await?.into_inner();

        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in ChannelOpenConfirm response".to_string())
        })?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "ChannelOpenConfirm: received unsigned CBOR (length: {}), port_id: {}, channel_id: {}",
            cbor_hex.len(),
            port_id,
            channel_id
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!(
                "MsgChannelOpenConfirm (port: {}, channel: {})",
                port_id, channel_id
            ),
        })
    }

    async fn build_channel_close_init_tx(
        &self,
        message_data: Vec<u8>,
    ) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::channel::v1::MsgChannelCloseInit;
        use prost::Message;

        let msg = MsgChannelCloseInit::decode(&message_data[..]).map_err(|e| {
            Error::Transaction(format!("Failed to decode MsgChannelCloseInit: {}", e))
        })?;

        let port_id = msg.port_id.clone();
        let channel_id = msg.channel_id.clone();

        let mut client = GenChannelMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.channel_close_init(request).await?.into_inner();

        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in ChannelCloseInit response".to_string())
        })?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "ChannelCloseInit: received unsigned CBOR (length: {}), port_id: {}, channel_id: {}",
            cbor_hex.len(),
            port_id,
            channel_id
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!(
                "MsgChannelCloseInit (port: {}, channel: {})",
                port_id, channel_id
            ),
        })
    }

    async fn build_channel_close_confirm_tx(
        &self,
        message_data: Vec<u8>,
    ) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::channel::v1::MsgChannelCloseConfirm;
        use prost::Message;

        let msg = MsgChannelCloseConfirm::decode(&message_data[..]).map_err(|e| {
            Error::Transaction(format!("Failed to decode MsgChannelCloseConfirm: {}", e))
        })?;

        let port_id = msg.port_id.clone();
        let channel_id = msg.channel_id.clone();

        let mut client = GenChannelMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.channel_close_confirm(request).await?.into_inner();

        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in ChannelCloseConfirm response".to_string())
        })?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "ChannelCloseConfirm: received unsigned CBOR (length: {}), port_id: {}, channel_id: {}",
            cbor_hex.len(),
            port_id,
            channel_id
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!(
                "MsgChannelCloseConfirm (port: {}, channel: {})",
                port_id, channel_id
            ),
        })
    }

    async fn build_recv_packet_tx(&self, message_data: Vec<u8>) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::channel::v1::MsgRecvPacket;
        use prost::Message;

        let msg = MsgRecvPacket::decode(&message_data[..])
            .map_err(|e| Error::Transaction(format!("Failed to decode MsgRecvPacket: {}", e)))?;

        let sequence = msg.packet.as_ref().map(|p| p.sequence).unwrap_or(0);

        let mut client = GenChannelMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.recv_packet(request).await?.into_inner();

        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in RecvPacket response".to_string())
        })?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "RecvPacket: received unsigned CBOR (length: {}), sequence: {}",
            cbor_hex.len(),
            sequence
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!("MsgRecvPacket (sequence: {})", sequence),
        })
    }

    async fn build_acknowledgement_tx(&self, message_data: Vec<u8>) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::channel::v1::MsgAcknowledgement;
        use prost::Message;

        let msg = MsgAcknowledgement::decode(&message_data[..]).map_err(|e| {
            Error::Transaction(format!("Failed to decode MsgAcknowledgement: {}", e))
        })?;

        let sequence = msg.packet.as_ref().map(|p| p.sequence).unwrap_or(0);

        let mut client = GenChannelMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.acknowledgement(request).await?.into_inner();

        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in Acknowledgement response".to_string())
        })?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "Acknowledgement: received unsigned CBOR (length: {}), sequence: {}",
            cbor_hex.len(),
            sequence
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!("MsgAcknowledgement (sequence: {})", sequence),
        })
    }

    async fn build_transfer_tx(&self, message_data: Vec<u8>) -> Result<UnsignedTx, Error> {
        use ibc_proto::ibc::applications::transfer::v1::MsgTransfer;
        use prost::Message;

        let msg = MsgTransfer::decode(&message_data[..])
            .map_err(|e| Error::Transaction(format!("Failed to decode MsgTransfer: {}", e)))?;

        if msg.token.is_none() {
            tracing::warn!(
                "MsgTransfer has no token payload from Hermes: source_port={} source_channel={} receiver={}",
                msg.source_port, msg.source_channel, msg.receiver
            );
        }

        let token_info = msg.token;
        let token = match token_info.as_ref() {
            Some(coin) => {
                let amount: u64 = coin.amount.parse().map_err(|e| {
                    Error::Transaction(format!(
                        "Invalid token amount in MsgTransfer (expected u64): {}",
                        e
                    ))
                })?;
                Some(super::generated::ibc::core::channel::v1::Coin {
                    denom: coin.denom.clone(),
                    amount,
                })
            }
            None => None,
        };

        let timeout_height =
            msg.timeout_height
                .map(|height| super::generated::ibc::core::client::v1::Height {
                    revision_number: height.revision_number,
                    revision_height: height.revision_height,
                });

        // The Gateway expects MsgTransfer under `ibc.core.channel.v1` and includes a `signer`
        // field. In canonical IBC, the sender is the signer for MsgTransfer.
        let sender = msg.sender;

        tracing::info!(
            "Preparing transfer request for gateway: source_port={} source_channel={} receiver={} sender={} token={:?} amount={:?} timeout_height={:?} timeout_timestamp={} memo_len={}",
            msg.source_port,
            msg.source_channel,
            msg.receiver,
            sender,
            token_info.as_ref().map(|coin| coin.denom.as_str()),
            token_info
                .as_ref()
                .and_then(|coin| coin.amount.parse::<u64>().ok()),
            timeout_height
                .as_ref()
                .map(|height| format!("{}-{}", height.revision_number, height.revision_height)),
            msg.timeout_timestamp,
            msg.memo.len(),
        );

        let gateway_msg = super::generated::ibc::core::channel::v1::MsgTransfer {
            source_port: msg.source_port,
            source_channel: msg.source_channel.clone(),
            token,
            sender: sender.clone(),
            receiver: msg.receiver,
            timeout_height,
            timeout_timestamp: msg.timeout_timestamp,
            memo: msg.memo,
            signer: sender,
        };

        let mut client = GenChannelMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(gateway_msg);

        let response = client.transfer(request).await?.into_inner();

        let unsigned_tx_any = response
            .unsigned_tx
            .ok_or_else(|| Error::Transaction("No unsigned_tx in Transfer response".to_string()))?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "Transfer: received unsigned CBOR (length: {}), source_channel: {}",
            cbor_hex.len(),
            msg.source_channel
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!("MsgTransfer (channel: {})", msg.source_channel),
        })
    }

    async fn build_timeout_tx(&self, message_data: Vec<u8>) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::channel::v1::MsgTimeout;
        use prost::Message;

        let msg = MsgTimeout::decode(&message_data[..])
            .map_err(|e| Error::Transaction(format!("Failed to decode MsgTimeout: {}", e)))?;

        let sequence = msg.packet.as_ref().map(|p| p.sequence).unwrap_or(0);

        let mut client = GenChannelMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.timeout(request).await?.into_inner();

        let unsigned_tx_any = response
            .unsigned_tx
            .ok_or_else(|| Error::Transaction("No unsigned_tx in Timeout response".to_string()))?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "Timeout: received unsigned CBOR (length: {}), sequence: {}",
            cbor_hex.len(),
            sequence
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!("MsgTimeout (sequence: {})", sequence),
        })
    }

    async fn build_timeout_on_close_tx(&self, message_data: Vec<u8>) -> Result<UnsignedTx, Error> {
        use super::generated::ibc::core::channel::v1::MsgTimeoutOnClose;
        use prost::Message;

        let msg = MsgTimeoutOnClose::decode(&message_data[..]).map_err(|e| {
            Error::Transaction(format!("Failed to decode MsgTimeoutOnClose: {}", e))
        })?;

        let sequence = msg.packet.as_ref().map(|p| p.sequence).unwrap_or(0);

        let mut client = GenChannelMsgClient::new(self.channel.clone());
        let request = tonic::Request::new(msg);

        let response = client.timeout_on_close(request).await?.into_inner();

        let unsigned_tx_any = response.unsigned_tx.ok_or_else(|| {
            Error::Transaction("No unsigned_tx in TimeoutOnClose response".to_string())
        })?;

        let cbor_hex = String::from_utf8(unsigned_tx_any.value)
            .map_err(|e| Error::Transaction(format!("Invalid UTF-8 in unsigned_tx: {}", e)))?;

        tracing::info!(
            "TimeoutOnClose: received unsigned CBOR (length: {}), sequence: {}",
            cbor_hex.len(),
            sequence
        );

        Ok(UnsignedTx {
            cbor_hex,
            description: format!("MsgTimeoutOnClose (sequence: {})", sequence),
        })
    }

    /// Submit a signed transaction to the Cardano blockchain via Gateway
    pub async fn submit_signed_tx(&self, signed_tx_cbor: &str) -> Result<TxSubmitResponse, Error> {
        tracing::info!(
            "Submitting signed transaction (CBOR length: {})",
            signed_tx_cbor.len()
        );

        let mut client = CardanoMsgClient::new(self.channel.clone());

        let request = tonic::Request::new(SubmitSignedTxRequest {
            signed_tx_cbor: signed_tx_cbor.to_string(),
            description: "Hermes IBC transaction".to_string(),
        });

        let response: SubmitSignedTxResponse = client.submit_signed_tx(request).await?.into_inner();

        // Parse height if present
        let height = if !response.height.is_empty() {
            let parts: Vec<&str> = response.height.split('-').collect();
            if parts.len() == 2 {
                let revision_number: u64 = parts[0].parse().unwrap_or(0);
                let revision_height: u64 = parts[1].parse().unwrap_or(0);
                Height::new(revision_number, revision_height).ok()
            } else {
                None
            }
        } else {
            None
        };

        // Convert proto events to IbcEvent
        let events = response
            .events
            .into_iter()
            .map(|e| IbcEvent {
                event_type: e.r#type,
                attributes: e.attributes.into_iter().map(|a| (a.key, a.value)).collect(),
            })
            .collect();

        Ok(TxSubmitResponse {
            tx_hash: response.tx_hash,
            height,
            events,
        })
    }

    /// Get the Gateway endpoint URL
    pub fn endpoint(&self) -> &str {
        &self.endpoint
    }

    /// Fetch a Mithril certificate for a specific chain point
    ///
    /// This should query the Gateway's Mithril aggregator endpoint to get:
    /// 1. The latest Mithril certificate covering the requested slot/epoch
    /// 2. The certificate chain back to genesis (if needed)
    /// 3. The multi-signature proof
    ///
    /// The certificate is used by the light client to verify Cardano block headers
    /// without needing to sync the full chain.
    ///
    /// TODO: Add custom proto for Mithril certificate query
    /// TODO: Implement certificate chain verification
    /// TODO: Cache certificates to avoid redundant queries
    pub async fn fetch_mithril_certificate(&self, slot: u64, epoch: u64) -> Result<Vec<u8>, Error> {
        tracing::info!(
            "Fetching Mithril certificate for slot={}, epoch={}",
            slot,
            epoch
        );

        // Stub implementation - requires custom Mithril proto
        tracing::warn!(
            "fetch_mithril_certificate: requires custom proto for Mithril aggregator endpoint"
        );
        Ok(vec![])
    }

    /// Query block header at a specific height
    pub async fn query_block_header(&self, _height: Height) -> Result<Vec<u8>, Error> {
        // TODO: Implement block header query
        tracing::warn!("query_block_header: stub implementation");
        Ok(vec![])
    }

    /// Query IBC events since a given height
    /// Returns events grouped by block height
    pub async fn query_events(
        &self,
        since_height: Height,
    ) -> Result<super::generated::ibc::cardano::v1::QueryEventsResponse, Error> {
        use super::generated::ibc::cardano::v1::{query_client::QueryClient, QueryEventsRequest};

        tracing::debug!("Querying events since height: {}", since_height);

        let mut client = QueryClient::new(self.channel.clone());
        let request = tonic::Request::new(QueryEventsRequest {
            since_height: since_height.revision_height(),
        });

        let response = client.events(request).await?.into_inner();

        tracing::debug!(
            "Received {} block events, current height: {}",
            response.events.len(),
            response.current_height
        );

        Ok(response)
    }
}
