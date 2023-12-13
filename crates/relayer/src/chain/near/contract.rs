use crate::chain::near::error::NearError;
use crate::chain::near::rpc::client::NearRpcClient;
use crate::chain::near::rpc::result::ViewResultDetails;
use crate::chain::requests::{
    QueryChannelsRequest, QueryPacketAcknowledgementsRequest, QueryPacketEventDataRequest,
    QueryPacketEventDataRequest1,
};
use crate::chain::requests::{
    QueryClientConnectionsRequest, QueryClientStatesRequest, QueryConnectionsRequest,
    QueryPacketCommitmentsRequest,
};
use crate::consensus_state::AnyConsensusState;
use alloc::sync::Arc;
use core::future::Future;
use ibc::core::handler::types::events::IbcEvent;
use ibc_relayer_types::core::ics02_client::height::Height;
use ibc_relayer_types::core::ics03_connection::connection::{
    ConnectionEnd, IdentifiedConnectionEnd,
};
use ibc_relayer_types::core::ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd};
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use near_primitives::types::AccountId;
use serde_json::json;
use std::fmt::{Debug, Display};
use tokio::runtime::Runtime as TokioRuntime;
use tracing::trace;

pub trait NearIbcContract {
    type Error: Send + Sync + 'static + Debug + Display + From<NearError>;

    fn get_contract_id(&self) -> AccountId;
    fn get_client(&self) -> &NearRpcClient;
    fn get_rt(&self) -> &Arc<TokioRuntime>;

    /// Run a future to completion on the Tokio runtime.
    fn block_on<F: Future>(&self, f: F) -> F::Output {
        self.get_rt().block_on(f)
    }

    fn view(
        &self,
        contract_id: AccountId,
        method_name: String,
        args: Vec<u8>,
    ) -> Result<ViewResultDetails, Self::Error> {
        self.block_on(self.get_client().view(contract_id, method_name, args))
            .map_err(Into::into)
    }

    fn get_latest_height(&self) -> Result<Height, Self::Error> {
        trace!("NearIbcContract: [get_latest_height]");

        let height: Height = self
            .view(
                self.get_contract_id(),
                "get_latest_height".into(),
                json!({}).to_string().into_bytes(),
            )?
            .json()?;

        // As we use solomachine client, we set the revision number to 0
        // TODO: ibc height reversion number is chainid version
        Height::new(0, height.revision_height())
            .map_err(NearError::build_ibc_height_error)
            .map_err(Into::into)
    }

    fn get_connection_end(
        &self,
        connection_identifier: &ConnectionId,
    ) -> Result<ConnectionEnd, Self::Error> {
        trace!(
            "connection_identifier: {:?} \n{}",
            connection_identifier,
            std::panic::Location::caller()
        );

        let connection_id = connection_identifier.to_string();

        self.view(
            self.get_contract_id(),
            "get_connection_end".into(),
            json!({ "connection_id": connection_id })
                .to_string()
                .into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    /// get channelEnd  by port_identifier, and channel_identifier
    fn get_channel_end(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<ChannelEnd, Self::Error> {
        trace!(
            "port_id: {:?} channel_id: {:?} \n{}",
            port_id,
            channel_id,
            std::panic::Location::caller()
        );

        self.view(
            self.get_contract_id(),
            "get_channel_end".into(),
            json!({"port_id": port_id, "channel_id": channel_id})
                .to_string()
                .into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    /// get client_state by client_id
    fn get_client_state(&self, client_id: &ClientId) -> Result<Vec<u8>, Self::Error> {
        trace!(
            "client_id: {:?} \n{}",
            client_id,
            std::panic::Location::caller()
        );

        self.view(
            self.get_contract_id(),
            "get_client_state".into(),
            json!({"client_id": client_id.clone()})
                .to_string()
                .into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_client_consensus_heights(
        &self,
        client_id: &ClientId,
    ) -> Result<Vec<Height>, Self::Error> {
        trace!(
            "client_id: {:?} \n{}",
            client_id,
            std::panic::Location::caller()
        );
        self.view(
            self.get_contract_id(),
            "get_client_consensus_heights".into(),
            json!({"client_id": client_id.clone()})
                .to_string()
                .into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    /// Performs a query to retrieve the consensus state for a specified height
    /// `consensus_height` that the specified light client stores.
    fn get_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: &Height,
    ) -> Result<Vec<u8>, Self::Error> {
        trace!(
            "client_id: {:?} consensus_height: {:?} \n{}",
            client_id,
            consensus_height,
            std::panic::Location::caller()
        );
        self.view(
            self.get_contract_id(),
            "get_client_consensus".into(),
            json!({"client_id": client_id.clone(), "consensus_height": consensus_height })
                .to_string()
                .into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_consensus_state_with_height(
        &self,
        client_id: &ClientId,
    ) -> Result<Vec<(Height, AnyConsensusState)>, Self::Error> {
        trace!(
            "client_id: {:?} \n{}",
            client_id,
            std::panic::Location::caller()
        );
        let client_id = serde_json::to_string(client_id).map_err(NearError::serde_json_error)?;

        self.view(
            self.get_contract_id(),
            "get_consensus_state_with_height".into(),
            json!({ "client_id": client_id }).to_string().into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_unreceipt_packet(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequences: &[Sequence],
    ) -> Result<Vec<u64>, Self::Error> {
        trace!(
            "port_id: {:?} channel_id: {:?} sequences: {:?} \n{}",
            port_id,
            channel_id,
            sequences,
            std::panic::Location::caller()
        );

        self.view(
            self.get_contract_id(),
            "get_unreceipt_packet".into(),
            json!({
                "port_id": port_id,
                "channel_id": channel_id,
                "sequences": sequences
            })
            .to_string()
            .into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<(ClientId, Vec<u8>)>, Self::Error> {
        trace!(
            "request: {:?} \n{}",
            request,
            std::panic::Location::caller()
        );

        let request = serde_json::to_string(&request).map_err(NearError::serde_json_error)?;

        self.view(
            self.get_contract_id(),
            "get_clients".into(),
            json!({ "request": request }).to_string().into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Self::Error> {
        trace!(
            "request: {:?} \n{}",
            request,
            std::panic::Location::caller()
        );

        let request = serde_json::to_string(&request).map_err(NearError::serde_json_error)?;

        self.view(
            self.get_contract_id(),
            "get_connections".into(),
            json!({ "request": request }).to_string().into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Self::Error> {
        trace!(
            "request: {:?} \n{}",
            request,
            std::panic::Location::caller()
        );

        let request = serde_json::to_string(&request).map_err(NearError::serde_json_error)?;

        self.view(
            self.get_contract_id(),
            "get_channels".into(),
            json!({ "request": request }).to_string().into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<Vec<Sequence>, Self::Error> {
        trace!(
            "request: {:?} \n{}",
            request,
            std::panic::Location::caller()
        );
        self.view(
            self.get_contract_id(),
            "get_packet_commitment_sequences".into(),
            json!({
                "port_id": request.port_id.to_string(),
                "channel_id": request.channel_id.to_string()
            })
            .to_string()
            .into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<Vec<Sequence>, Self::Error> {
        trace!("NearIbcContract: [get_packet_acknowledgements]");

        self.view(
            self.get_contract_id(),
            "get_packet_acknowledgement_sequences".into(),
            json!({
                "port_id": request.port_id.to_string(),
                "channel_id": request.channel_id.to_string()
            })
            .to_string()
            .into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    /// get connection_identifier vector by client_identifier
    fn get_client_connections(
        &self,
        request: &QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Self::Error> {
        let client_id = request.client_id.to_string();
        trace!(
            "client_id: {:?} \n{}",
            client_id,
            std::panic::Location::caller()
        );
        self.view(
            self.get_contract_id(),
            "get_client_connections".into(),
            json!({ "client_id": client_id }).to_string().into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_connection_channels(
        &self,
        connection_id: &ConnectionId,
    ) -> Result<Vec<IdentifiedChannelEnd>, Self::Error> {
        trace!(
            "connection_id: {:?} \n{}",
            connection_id,
            std::panic::Location::caller()
        );

        self.view(
            self.get_contract_id(),
            "get_connection_channels".into(),
            json!({ "connection_id": connection_id.to_string() })
                .to_string()
                .into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_packet_commitment(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: &Sequence,
    ) -> Result<Vec<u8>, Self::Error> {
        trace!(
            "port_id: {:?}, channel_id: {:?}, sequence: {:?} \n{}",
            port_id,
            channel_id,
            sequence,
            std::panic::Location::caller()
        );

        self.view(
            self.get_contract_id(),
            "get_packet_commitment".into(),
            json!({
                "port_id": port_id,
                "channel_id": channel_id,
               "sequence": sequence
            })
            .to_string()
            .into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_commitment_prefix(&self) -> Result<Vec<u8>, Self::Error> {
        trace!("NearIbcContract: [get_commitment_prefix]");
        self.view(
            self.get_contract_id(),
            "get_commitment_prefix".into(),
            json!({}).to_string().into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_contract_version(&self) -> Result<Vec<u8>, Self::Error> {
        trace!("NearIbcContract: [get_contract_version]");

        self.view(
            self.get_contract_id(),
            "version".into(),
            json!({}).to_string().into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_packet_receipt(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: &Sequence,
    ) -> Result<Vec<u8>, Self::Error> {
        trace!(
            "port_id: {:?}, channel_id: {:?}, sequence: {:?} \n{}",
            port_id,
            channel_id,
            sequence,
            std::panic::Location::caller()
        );

        self.view(
            self.get_contract_id(),
            "get_packet_receipt".into(),
            json!({
                "port_id": port_id,
                "channel_id": channel_id,
                "sequence": sequence
            })
            .to_string()
            .into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_next_sequence_receive(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
    ) -> Result<Sequence, Self::Error> {
        trace!(
            "port_id: {:?}, channel_id: {:?} \n{}",
            port_id,
            channel_id,
            std::panic::Location::caller()
        );

        self.view(
            self.get_contract_id(),
            "get_next_sequence_receive".into(),
            json!({
                "port_id": port_id,
                "channel_id": channel_id,
            })
            .to_string()
            .into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_packet_acknowledgement(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: &Sequence,
    ) -> Result<Vec<u8>, Self::Error> {
        trace!(
            "port_id: {:?}, channel_id: {:?}, sequence: {:?} \n{}",
            port_id,
            channel_id,
            sequence,
            std::panic::Location::caller()
        );

        self.view(
            self.get_contract_id(),
            "get_packet_acknowledgement".into(),
            json!({
                "port_id": port_id,
                "channel_id": channel_id,
                "sequence": sequence
            })
            .to_string()
            .into_bytes(),
        )?
        .json()
        .map_err(Into::into)
    }

    fn get_packet_events(
        &self,
        request: QueryPacketEventDataRequest,
    ) -> Result<Vec<(Height, Vec<IbcEvent>)>, Self::Error> {
        trace!(
            "request: {:?} \n{}",
            request,
            std::panic::Location::caller()
        );

        let req = QueryPacketEventDataRequest1 {
            event_type: request.event_id.as_str().to_owned(),
            source_channel_id: request.source_channel_id,
            source_port_id: request.source_port_id,
            destination_channel_id: request.destination_channel_id,
            destination_port_id: request.destination_port_id,
            sequences: request.sequences,
            height: request.height,
        };

        self.view(
            self.get_contract_id(),
            "get_packet_events".into(),
            json!({ "request": req }).to_string().into_bytes(),
        )?
        .json::<Vec<(Height, Vec<IbcEvent>)>>()
        .map_err(Into::into)
    }
}

#[tokio::test]
pub async fn test123() -> anyhow::Result<()> {
    const CONTRACT_ACCOUNT_ID: &str = "v3.nearibc.testnet";
    let client =
        NearRpcClient::new("https://near-testnet.infura.io/v3/4f80a04e6eb2437a9ed20cb874e10d55");
    let connection_id = ConnectionId::new(5);
    let connection_id = serde_json::to_string(&connection_id).unwrap();
    dbg!(&connection_id);

    dbg!(&connection_id.eq("connection-5"));
    let result = client
        .view(
            CONTRACT_ACCOUNT_ID.parse()?,
            "get_connection_end".to_string(),
            json!({"connection_id": "connection-5".to_string()})
                .to_string()
                .into_bytes(),
        )
        .await
        .map_err(|e| NearError::custom_error(e.to_string()))?;

    let result_raw: serde_json::value::Value = result.json().unwrap();
    dbg!(&result_raw);
    let connection_end: ConnectionEnd =
        serde_json::from_value(result_raw).map_err(NearError::serde_json_error)?;
    dbg!(&connection_end);
    Ok(())
}
