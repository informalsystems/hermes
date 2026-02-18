use prost::Message;
use serde_derive::{Deserialize, Serialize};

use ibc_proto::google::protobuf::Any;
use ibc_proto::Protobuf;

use crate::clients::ics08_cardano::error::Error;
use crate::clients::ics08_cardano::raw;
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::consensus_state::ConsensusState as Ics2ConsensusState;
use crate::core::ics02_client::error::Error as Ics02Error;
use crate::core::ics23_commitment::commitment::CommitmentRoot;
use crate::timestamp::Timestamp;

pub const MITHRIL_CONSENSUS_STATE_TYPE_URL: &str = "/ibc.lightclients.mithril.v1.ConsensusState";
pub const LEGACY_MITHRIL_CONSENSUS_STATE_TYPE_URL: &str = "/ibc.clients.mithril.v1.ConsensusState";

type RawConsensusState = raw::ConsensusState;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsensusState {
    pub root: CommitmentRoot,
    pub timestamp: u64,
    pub first_cert_hash_latest_epoch: raw::MithrilCertificate,
    pub latest_cert_hash_tx_snapshot: String,
}

impl ConsensusState {
    pub fn new(
        root: CommitmentRoot,
        timestamp: u64,
        first_cert_hash_latest_epoch: raw::MithrilCertificate,
        latest_cert_hash_tx_snapshot: String,
    ) -> Self {
        Self {
            root,
            timestamp,
            first_cert_hash_latest_epoch,
            latest_cert_hash_tx_snapshot,
        }
    }
}

impl Ics2ConsensusState for ConsensusState {
    fn client_type(&self) -> ClientType {
        ClientType::Cardano
    }

    fn root(&self) -> &CommitmentRoot {
        &self.root
    }

    fn timestamp(&self) -> Timestamp {
        Timestamp::from_nanoseconds(self.timestamp).unwrap_or_else(|_| Timestamp::none())
    }
}

impl Protobuf<RawConsensusState> for ConsensusState {}

impl TryFrom<RawConsensusState> for ConsensusState {
    type Error = Error;

    fn try_from(raw: RawConsensusState) -> Result<Self, Self::Error> {
        let RawConsensusState {
            timestamp,
            first_cert_hash_latest_epoch,
            latest_cert_hash_tx_snapshot,
            ibc_state_root,
        } = raw;

        let first = first_cert_hash_latest_epoch
            .ok_or_else(|| Error::missing_field("first_cert_hash_latest_epoch"))?;

        // Legacy Cosmos demo chains may omit `ibc_state_root` from stored consensus states.
        // Keep decode compatibility by deriving a stable 32-byte placeholder from the latest
        // transaction snapshot hash when possible, and fall back to zero bytes otherwise.
        let normalized_root = if ibc_state_root.is_empty() {
            if latest_cert_hash_tx_snapshot.len() == 64 {
                decode_hex_to_bytes(&latest_cert_hash_tx_snapshot)
                    .unwrap_or_else(|| vec![0u8; 32])
            } else {
                vec![0u8; 32]
            }
        } else {
            ibc_state_root
        };

        if normalized_root.len() != 32 {
            return Err(Error::invalid_field(
                "ibc_state_root",
                format!("expected 32 bytes, got {}", normalized_root.len()),
            ));
        }

        let root = CommitmentRoot::from_bytes(&normalized_root);

        Ok(Self::new(
            root,
            timestamp,
            first,
            latest_cert_hash_tx_snapshot,
        ))
    }
}

impl From<ConsensusState> for RawConsensusState {
    fn from(value: ConsensusState) -> Self {
        RawConsensusState {
            timestamp: value.timestamp,
            first_cert_hash_latest_epoch: Some(value.first_cert_hash_latest_epoch),
            latest_cert_hash_tx_snapshot: value.latest_cert_hash_tx_snapshot,
            ibc_state_root: value.root.as_bytes().to_vec(),
        }
    }
}

fn decode_hex_to_bytes(input: &str) -> Option<Vec<u8>> {
    if input.len() % 2 != 0 {
        return None;
    }

    let mut out = Vec::with_capacity(input.len() / 2);
    for index in (0..input.len()).step_by(2) {
        let pair = &input[index..index + 2];
        let value = u8::from_str_radix(pair, 16).ok()?;
        out.push(value);
    }
    Some(out)
}

impl Protobuf<Any> for ConsensusState {}

impl TryFrom<Any> for ConsensusState {
    type Error = Ics02Error;

    fn try_from(raw_any: Any) -> Result<Self, Ics02Error> {
        use core::ops::Deref;

        fn decode_state(bytes: &[u8]) -> Result<ConsensusState, Error> {
            RawConsensusState::decode(bytes)
                .map_err(Error::decode)?
                .try_into()
        }

        match raw_any.type_url.as_str() {
            MITHRIL_CONSENSUS_STATE_TYPE_URL | LEGACY_MITHRIL_CONSENSUS_STATE_TYPE_URL => {
                decode_state(raw_any.value.deref()).map_err(Into::into)
            }
            _ => Err(Ics02Error::unknown_consensus_state_type(raw_any.type_url)),
        }
    }
}

impl From<ConsensusState> for Any {
    fn from(value: ConsensusState) -> Self {
        Any {
            type_url: MITHRIL_CONSENSUS_STATE_TYPE_URL.to_string(),
            value: Protobuf::<RawConsensusState>::encode_vec(value),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use test_log::test;

    fn raw_certificate() -> raw::MithrilCertificate {
        raw::MithrilCertificate {
            hash: "cert_hash".to_string(),
            previous_hash: "".to_string(),
            epoch: 0,
            signed_entity_type: None,
            metadata: None,
            protocol_message: None,
            signed_message: "".to_string(),
            aggregate_verification_key: "".to_string(),
            multi_signature: "".to_string(),
            genesis_signature: "".to_string(),
        }
    }

    fn raw_consensus_state() -> raw::ConsensusState {
        raw::ConsensusState {
            timestamp: 1,
            first_cert_hash_latest_epoch: Some(raw_certificate()),
            latest_cert_hash_tx_snapshot: "latest".to_string(),
            ibc_state_root: vec![0u8; 32],
        }
    }

    #[test]
    fn mithril_consensus_state_any_roundtrip() {
        let state = ConsensusState::try_from(raw_consensus_state()).unwrap();
        let any: Any = state.clone().into();
        let decoded = ConsensusState::try_from(any).unwrap();

        assert_eq!(decoded, state);
        assert_eq!(decoded.root.as_bytes().len(), 32);
    }

    #[test]
    fn mithril_consensus_state_invalid_root_length_fails() {
        let mut raw = raw_consensus_state();
        raw.ibc_state_root = vec![0u8; 31];

        let err = ConsensusState::try_from(raw).unwrap_err();
        assert!(err
            .to_string()
            .contains("invalid field ibc_state_root: expected 32 bytes, got 31"));
    }
}
