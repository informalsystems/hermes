use ibc_proto::google::protobuf::Any;
use ibc_proto::Protobuf;
use prost::Message;
use serde::{Deserialize, Serialize};

use crate::clients::ics10_stellar::error::Error;
use crate::clients::ics10_stellar::raw::{RawConsensusState, STELLAR_CONSENSUS_STATE_TYPE_URL};
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::consensus_state::ConsensusState as Ics2ConsensusState;
use crate::core::ics02_client::error::Error as Ics02Error;
use crate::core::ics23_commitment::commitment::CommitmentRoot;
use crate::timestamp::Timestamp;

/// Stellar IBC consensus state.
///
/// The `root` field holds the `bucketListHash` from the Stellar `LedgerHeader`.
/// This is the closest analogue to a state root — it commits to the full
/// on-chain state at a given ledger. Note that Stellar does not provide native
/// Merkle inclusion proofs against this root; IBC verification on Stellar
/// relies on SCP consensus proofs instead.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsensusState {
    /// Commitment root: the `bucketListHash` from the Stellar `LedgerHeader` (32 bytes)
    pub root: CommitmentRoot,
    /// Ledger close timestamp
    pub timestamp: Timestamp,
    /// Stellar ledger sequence number
    pub ledger_seq: u32,
}

impl ConsensusState {
    pub fn new(root: CommitmentRoot, timestamp: Timestamp, ledger_seq: u32) -> Self {
        Self {
            root,
            timestamp,
            ledger_seq,
        }
    }
}

impl Ics2ConsensusState for ConsensusState {
    fn client_type(&self) -> ClientType {
        ClientType::Stellar
    }

    fn root(&self) -> &CommitmentRoot {
        &self.root
    }

    fn timestamp(&self) -> Timestamp {
        self.timestamp
    }
}

// ---------------------------------------------------------------------------
// Protobuf conversions
// ---------------------------------------------------------------------------

impl Protobuf<RawConsensusState> for ConsensusState {}

impl TryFrom<RawConsensusState> for ConsensusState {
    type Error = Error;

    fn try_from(raw: RawConsensusState) -> Result<Self, Self::Error> {
        if raw.root.len() != 32 {
            return Err(Error::invalid_raw_consensus_state(
                "root must be exactly 32 bytes (bucketListHash)".into(),
            ));
        }

        let timestamp = Timestamp::from_nanoseconds(raw.timestamp_ns)
            .map_err(|e| Error::invalid_raw_consensus_state(e.to_string()))?;

        Ok(Self {
            root: CommitmentRoot::from_bytes(&raw.root),
            timestamp,
            ledger_seq: raw.ledger_seq,
        })
    }
}

impl From<ConsensusState> for RawConsensusState {
    fn from(value: ConsensusState) -> Self {
        Self {
            root: value.root.into_vec(),
            timestamp_ns: value.timestamp.nanoseconds(),
            ledger_seq: value.ledger_seq,
        }
    }
}

impl Protobuf<Any> for ConsensusState {}

impl TryFrom<Any> for ConsensusState {
    type Error = Ics02Error;

    fn try_from(raw: Any) -> Result<Self, Self::Error> {
        match raw.type_url.as_str() {
            STELLAR_CONSENSUS_STATE_TYPE_URL => RawConsensusState::decode(raw.value.as_ref())
                .map_err(|e| Error::decode(e.into()))?
                .try_into()
                .map_err(Into::into),
            _ => Err(Ics02Error::unknown_consensus_state_type(raw.type_url)),
        }
    }
}

impl From<ConsensusState> for Any {
    fn from(value: ConsensusState) -> Self {
        Any {
            type_url: STELLAR_CONSENSUS_STATE_TYPE_URL.to_string(),
            value: Protobuf::<RawConsensusState>::encode_vec(value),
        }
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use ibc_proto::google::protobuf::Any;

    use super::ConsensusState;
    use crate::clients::ics10_stellar::raw::{RawConsensusState, STELLAR_CONSENSUS_STATE_TYPE_URL};
    use crate::core::ics02_client::client_type::ClientType;
    use crate::core::ics02_client::consensus_state::ConsensusState as Ics2ConsensusState;
    use crate::core::ics23_commitment::commitment::CommitmentRoot;
    use crate::timestamp::Timestamp;

    fn sample_consensus_state() -> ConsensusState {
        ConsensusState::new(
            CommitmentRoot::from_bytes(&[0xcd; 32]),
            Timestamp::from_nanoseconds(1_700_000_000_000_000_000).unwrap(),
            5000,
        )
    }

    #[test]
    fn client_type_is_stellar() {
        assert_eq!(sample_consensus_state().client_type(), ClientType::Stellar);
    }

    #[test]
    fn accessors() {
        let cs = sample_consensus_state();
        assert_eq!(cs.root(), &CommitmentRoot::from_bytes(&[0xcd; 32]));
        assert_eq!(
            cs.timestamp(),
            Timestamp::from_nanoseconds(1_700_000_000_000_000_000).unwrap()
        );
        assert_eq!(cs.ledger_seq, 5000);
    }

    #[test]
    fn roundtrip_raw() {
        let original = sample_consensus_state();
        let raw = RawConsensusState::from(original.clone());
        let recovered = ConsensusState::try_from(raw).unwrap();
        assert_eq!(original, recovered);
    }

    #[test]
    fn roundtrip_any() {
        let original = sample_consensus_state();
        let any = Any::from(original.clone());
        assert_eq!(any.type_url, STELLAR_CONSENSUS_STATE_TYPE_URL);
        let recovered = ConsensusState::try_from(any).unwrap();
        assert_eq!(original, recovered);
    }

    #[test]
    fn wrong_root_length_returns_error() {
        let raw = RawConsensusState {
            root: vec![0u8; 16], // wrong: must be 32 bytes
            timestamp_ns: 1_000_000,
            ledger_seq: 1,
        };
        assert!(ConsensusState::try_from(raw).is_err());
    }

    #[test]
    fn unknown_type_url_returns_error() {
        let any = Any {
            type_url: "/some.other.ConsensusState".to_string(),
            value: vec![],
        };
        assert!(ConsensusState::try_from(any).is_err());
    }
}
