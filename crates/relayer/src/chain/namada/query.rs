use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics23_commitment::merkle::convert_tm_to_ics_merkle_proof;
use ibc_relayer_types::core::ics23_commitment::merkle::MerkleProof;
use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::Height as ICSHeight;
use namada::ledger::events::EventType as NamadaEventType;
use namada::ledger::queries::RPC;
use namada::tendermint::block::Height as TmHeight;
use namada::tendermint_rpc::Client;
use namada::types::storage::{BlockHeight, Epoch, Key, PrefixValue};
use tendermint::abci::{Event, EventAttribute};
use tendermint::merkle::proof::{ProofOp, ProofOps};

use crate::chain::requests::{QueryClientEventRequest, QueryHeight, QueryPacketEventDataRequest};
use crate::error::Error;
use crate::event::{ibc_event_try_from_abci_event, IbcEventWithHeight};

use super::NamadaChain;
use crate::chain::endpoint::ChainEndpoint;
use crate::chain::requests::IncludeProof;

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
        let response = self
            .rt
            .block_on(
                RPC.shell()
                    .storage_value(&self.rpc_client, None, height, is_proven, &key),
            )
            .map_err(|e| Error::namada_query(e.to_string()))?;

        let proof = if is_proven {
            let proof_ops = response.proof.ok_or_else(Error::empty_response_proof)?;
            // convert MerkleProof to one of the base tendermint
            let ops: Vec<ProofOp> = proof_ops
                .ops
                .iter()
                .map(|proof_op| ProofOp {
                    field_type: proof_op.field_type.clone(),
                    key: proof_op.key.clone(),
                    data: proof_op.data.clone(),
                })
                .collect();
            let tm_proof_ops = ProofOps { ops };
            let proof = convert_tm_to_ics_merkle_proof(&tm_proof_ops).map_err(Error::ics23)?;
            Some(proof)
        } else {
            None
        };

        Ok((response.data, proof))
    }

    pub fn query_prefix(&self, prefix: Key) -> Result<Vec<PrefixValue>, Error> {
        let response = self
            .rt
            .block_on(
                RPC.shell()
                    .storage_prefix(&self.rpc_client, None, None, false, &prefix),
            )
            .map_err(|e| Error::namada_query(e.to_string()))?;
        Ok(response.data)
    }

    pub fn query_epoch(&self) -> Result<Epoch, Error> {
        self.rt
            .block_on(RPC.shell().epoch(&self.rpc_client))
            .map_err(|e| Error::namada_query(e.to_string()))
    }

    pub fn query_update_event(
        &self,
        request: &QueryClientEventRequest,
    ) -> Result<Option<IbcEventWithHeight>, Error> {
        let height = BlockHeight(request.consensus_height.revision_height());
        let event = self
            .rt
            .block_on(RPC.shell().ibc_client_update(
                &self.rpc_client,
                &request.client_id.as_str().parse().unwrap(),
                &height,
            ))
            .map_err(|e| Error::namada_query(e.to_string()))?;
        match event {
            Some(event) => {
                let h = event
                    .get("height")
                    .expect("No height in the Namada event")
                    .parse()
                    .map_err(|_| Error::invalid_height_no_source())?;
                let height = ICSHeight::new(self.config.id.version(), h)
                    .map_err(|_| Error::invalid_height_no_source())?;
                match into_ibc_event(event) {
                    Some(event) => Ok(Some(IbcEventWithHeight { event, height })),
                    // non IBC event
                    None => Ok(None),
                }
            }
            None => Ok(None),
        }
    }

    /// Get all IBC events when the tx has been applied
    pub fn query_tx_events(&self, tx_hash: &str) -> Result<Vec<IbcEventWithHeight>, Error> {
        match self.query_tx_height(tx_hash)? {
            Some(height) => self.query_events(height),
            None => Ok(vec![]),
        }
    }

    /// Get the height at which the tx has been applied
    fn query_tx_height(&self, tx_hash: &str) -> Result<Option<ICSHeight>, Error> {
        match self
            .rt
            .block_on(RPC.shell().applied(
                &self.rpc_client,
                &tx_hash.try_into().expect("Invalid tx hash"),
            ))
            .map_err(|e| Error::namada_query(e.to_string()))?
        {
            Some(applied) => {
                let h = applied
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
                    &self.rpc_client,
                    &request
                        .event_id
                        .as_str()
                        .parse()
                        .expect("invalid event type"),
                    &request.source_port_id.as_str().parse().unwrap(),
                    &request.source_channel_id.as_str().parse().unwrap(),
                    &request.destination_port_id.as_str().parse().unwrap(),
                    &request.destination_channel_id.as_str().parse().unwrap(),
                    &namada::ibc::core::ics04_channel::packet::Sequence::from(u64::from(sequence)),
                ),
            )
            .map_err(|e| Error::namada_query(e.to_string()))?
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
            .block_on(self.rpc_client.block_results(tm_height))
            .map_err(|e| Error::abci_plus_rpc(self.config.rpc_addr.clone(), e))?;

        let events = response
            .end_block_events
            .ok_or_else(|| Error::query("No transaction result was found".to_string()))?;
        let mut ibc_events = vec![];
        for event in &events {
            let event = into_abci_event(event);
            match ibc_event_try_from_abci_event(&event) {
                Ok(e) => ibc_events.push(IbcEventWithHeight::new(e, height)),
                Err(_) => {
                    // check the transaction result
                    if event.kind == NamadaEventType::Applied.to_string() {
                        let success_code_tag = EventAttribute {
                            key: "code".to_string(),
                            value: "0".to_string(),
                            index: true,
                        };
                        if !event.attributes.contains(&success_code_tag) {
                            let ibc_event = IbcEventWithHeight::new(
                                IbcEvent::ChainError(format!(
                                    "The transaction was invalid: Event {:?}",
                                    event,
                                )),
                                height,
                            );
                            ibc_events.push(ibc_event);
                        }
                    }
                    // skip special ibc-rs events
                }
            }
        }
        Ok(ibc_events)
    }
}

fn into_abci_event(event: &namada::tendermint::abci::Event) -> Event {
    let attributes = event
        .attributes
        .iter()
        .map(|tag| EventAttribute {
            key: tag.key.to_string(),
            value: tag.value.to_string(),
            index: true,
        })
        .collect();

    Event {
        kind: event.type_str.clone(),
        attributes,
    }
}

fn into_ibc_event(namada_event: namada::ledger::events::Event) -> Option<IbcEvent> {
    let attributes = namada_event
        .attributes
        .into_iter()
        .map(|(key, value)| EventAttribute {
            key,
            value,
            index: true,
        })
        .collect();
    let abci_event = Event {
        kind: namada_event.event_type.to_string(),
        attributes,
    };
    match ibc_event_try_from_abci_event(&abci_event) {
        Ok(ibc_event) => Some(ibc_event),
        // non IBC event
        Err(_) => None,
    }
}
