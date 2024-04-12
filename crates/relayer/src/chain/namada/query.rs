use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics23_commitment::merkle::convert_tm_to_ics_merkle_proof;
use ibc_relayer_types::core::ics23_commitment::merkle::MerkleProof;
use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::Height as ICSHeight;
use namada_ibc::storage::{ibc_trace_key_prefix, is_ibc_trace_key};
use namada_sdk::address::{Address, InternalAddress};
use namada_sdk::borsh::BorshDeserialize;
use namada_sdk::queries::{Client as SdkClient, RPC};
use namada_sdk::rpc;
use namada_sdk::storage::{BlockHeight, Epoch, Key, PrefixValue};
use namada_sdk::Namada;
use tendermint::block::Height as TmHeight;

use crate::chain::endpoint::ChainEndpoint;
use crate::chain::requests::{
    IncludeProof, QueryClientEventRequest, QueryHeight, QueryPacketEventDataRequest,
};
use crate::error::Error;
use crate::event::{ibc_event_try_from_abci_event, IbcEventWithHeight};

use super::error::Error as NamadaError;
use super::NamadaChain;

impl NamadaChain {
    pub fn query(
        &self,
        key: Key,
        height: QueryHeight,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        let height = match height {
            QueryHeight::Latest => None,
            QueryHeight::Specific(h) => Some(BlockHeight(h.revision_height())),
        };
        let is_proven = matches!(include_proof, IncludeProof::Yes);
        let (value, proof) = self
            .rt
            .block_on(rpc::query_storage_value_bytes(
                self.ctx.client(),
                &key,
                height,
                is_proven,
            ))
            .map_err(NamadaError::namada)?;

        let proof = if is_proven {
            let proof_ops = proof.ok_or_else(Error::empty_response_proof)?;
            let proof = convert_tm_to_ics_merkle_proof(&proof_ops).map_err(Error::ics23)?;
            Some(proof)
        } else {
            None
        };
        // return an empty data for non-existence proof
        Ok((value.unwrap_or_default(), proof))
    }

    pub fn query_prefix(&self, prefix: Key) -> Result<Vec<PrefixValue>, Error> {
        let response = self
            .rt
            .block_on(
                // We can't use rpc::query_storage_prefix` because we need byte data
                RPC.shell()
                    .storage_prefix(self.ctx.client(), None, None, false, &prefix),
            )
            .map_err(NamadaError::query)?;
        Ok(response.data)
    }

    pub fn query_epoch(&self) -> Result<Epoch, Error> {
        self.rt
            .block_on(rpc::query_epoch(self.ctx.client()))
            .map_err(|e| Error::namada(NamadaError::namada(e)))
    }

    pub fn query_update_event(
        &self,
        request: &QueryClientEventRequest,
    ) -> Result<Option<IbcEventWithHeight>, Error> {
        let height = BlockHeight(request.consensus_height.revision_height());
        let event = self
            .rt
            .block_on(RPC.shell().ibc_client_update(
                self.ctx.client(),
                &request.client_id.as_str().parse().unwrap(),
                &height,
            ))
            .map_err(NamadaError::query)?;
        match event {
            Some(event) => {
                let h = event
                    .get("height")
                    .expect("No height in the Namada event")
                    .parse()
                    .map_err(|_| Error::invalid_height_no_source())?;
                let height = ICSHeight::new(self.config.id.version(), h)
                    .map_err(|_| Error::invalid_height_no_source())?;
                let pb_abci_event = tendermint_proto::v0_37::abci::Event::from(event);
                let abci_event = pb_abci_event.try_into().map_err(|_| {
                    Error::query("Conversion from proto AbciEvent to AbciEvent failed".to_string())
                })?;
                match ibc_event_try_from_abci_event(&abci_event) {
                    Ok(event) => Ok(Some(IbcEventWithHeight { event, height })),
                    // non IBC event
                    Err(_) => Ok(None),
                }
            }
            None => Ok(None),
        }
    }

    /// Get all IBC events when the tx has been applied
    pub fn query_tx_events(&self, tx_hash: &str) -> Result<Vec<IbcEventWithHeight>, Error> {
        match self
            .rt
            .block_on(RPC.shell().applied(
                self.ctx.client(),
                &tx_hash.try_into().expect("Invalid tx hash"),
            ))
            .map_err(NamadaError::query)?
        {
            Some(applied) => {
                let h = applied
                    .get("height")
                    .expect("No height in the Namada Applied event")
                    .parse()
                    .map_err(|_| Error::invalid_height_no_source())?;
                let height = ICSHeight::new(self.config.id.version(), h)
                    .map_err(|_| Error::invalid_height_no_source())?;
                // Check if the tx is valid
                let code = applied.get("code").expect("The code should exist");
                if code != "0" {
                    return Ok(vec![IbcEventWithHeight::new(
                        IbcEvent::ChainError(format!(
                            "The transaction was invalid: Event {:?}",
                            applied,
                        )),
                        height,
                    )]);
                }
                self.query_events(height)
            }
            None => Ok(vec![]),
        }
    }

    /// Get IBC packet events
    pub fn query_packet_events_from_block(
        &self,
        request: &QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        let mut block_events = vec![];
        for seq in &request.sequences {
            if let Some(response_height) = self.query_packet_height(request, *seq)? {
                if let QueryHeight::Specific(query_height) = request.height.get() {
                    if response_height > query_height {
                        continue;
                    }
                }
                let events = self.query_events(response_height)?;
                let mut packet_events = events
                    .into_iter()
                    .filter(|e| {
                        let packet = match &e.event {
                            IbcEvent::SendPacket(send_event) => &send_event.packet,
                            IbcEvent::WriteAcknowledgement(write_ack_event) => {
                                &write_ack_event.packet
                            }
                            _ => return false,
                        };
                        !block_events.contains(e)
                            && packet.source_port == request.source_port_id
                            && packet.source_channel == request.source_channel_id
                            && packet.destination_port == request.destination_port_id
                            && packet.destination_channel == request.destination_channel_id
                            && packet.sequence == *seq
                    })
                    .collect();
                block_events.append(&mut packet_events);
            }
        }
        Ok(block_events)
    }

    /// Get the height at which the packet event has been emitted
    fn query_packet_height(
        &self,
        request: &QueryPacketEventDataRequest,
        sequence: Sequence,
    ) -> Result<Option<ICSHeight>, Error> {
        match self
            .rt
            .block_on(
                RPC.shell().ibc_packet(
                    self.ctx.client(),
                    &request
                        .event_id
                        .as_str()
                        .parse()
                        .expect("invalid event type"),
                    &request
                        .source_port_id
                        .as_str()
                        .parse()
                        .expect("PortId should be parsable"),
                    &request
                        .source_channel_id
                        .as_str()
                        .parse()
                        .expect("ChannelId should be parsable"),
                    &request
                        .destination_port_id
                        .as_str()
                        .parse()
                        .expect("PortId should be parsable"),
                    &request
                        .destination_channel_id
                        .as_str()
                        .parse()
                        .expect("ChannelId should be parsable"),
                    &u64::from(sequence).into(),
                ),
            )
            .map_err(NamadaError::query)?
        {
            Some(event) => {
                let h = event
                    .get("height")
                    .expect("No height in the Namada Applied event")
                    .parse()
                    .map_err(|_| Error::invalid_height_no_source())?;
                let height = ICSHeight::new(self.config.id.version(), h)
                    .map_err(|_| Error::invalid_height_no_source())?;
                Ok(Some(height))
            }
            None => Ok(None),
        }
    }

    /// Get IBC events at the given height
    fn query_events(&self, height: ICSHeight) -> Result<Vec<IbcEventWithHeight>, Error> {
        crate::time!(
            "query_blocks: query block packet events",
            {
                "src_chain": self.config().id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_block");

        let tm_height = TmHeight::try_from(height.revision_height())
            .map_err(|_| Error::invalid_height_no_source())?;
        let response = self
            .rt
            .block_on(SdkClient::block_results(self.ctx.client(), tm_height))
            .map_err(|e| Error::rpc(self.config.rpc_addr.clone(), e))?;

        let events = response
            .end_block_events
            .ok_or_else(|| Error::query("No transaction result was found".to_string()))?;
        let mut ibc_events = vec![];
        for event in &events {
            if let Ok(ibc_event) = ibc_event_try_from_abci_event(event) {
                ibc_events.push(IbcEventWithHeight::new(ibc_event, height))
            }
        }
        Ok(ibc_events)
    }

    /// Get IBC denom
    pub fn query_denom(&self, raw_addr: String) -> Result<String, Error> {
        let token = Address::decode(&raw_addr)
            .map_err(|_| NamadaError::address_decode(raw_addr.to_string()))?;
        let hash = match &token {
            Address::Internal(InternalAddress::IbcToken(hash)) => hash.to_string(),
            _ => return Err(NamadaError::denom_not_found(raw_addr).into()),
        };

        let prefix = ibc_trace_key_prefix(None);
        let pairs = self.query_prefix(prefix)?;
        let pair = pairs
            .iter()
            .find(|PrefixValue { key, value: _ }| {
                if let Some((_, token_hash)) = is_ibc_trace_key(key) {
                    token_hash == *hash
                } else {
                    false
                }
            })
            .ok_or(NamadaError::denom_not_found(raw_addr))?;

        String::try_from_slice(&pair.value).map_err(|e| Error::namada(NamadaError::borsh_decode(e)))
    }
}
