/// ClientState from Tendermint tracks the current validator set, latest height,
/// and a possible frozen height.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ClientState {
    #[prost(string, tag="1")]
    pub chain_id: ::prost::alloc::string::String,
    #[prost(message, optional, tag="2")]
    pub trust_level: ::core::option::Option<Fraction>,
    /// duration of the period since the LastestTimestamp during which the
    /// submitted headers are valid for upgrade
    #[prost(message, optional, tag="3")]
    pub trusting_period: ::core::option::Option<super::super::super::super::google::protobuf::Duration>,
    /// duration of the staking unbonding period
    #[prost(message, optional, tag="4")]
    pub unbonding_period: ::core::option::Option<super::super::super::super::google::protobuf::Duration>,
    /// defines how much new (untrusted) header's Time can drift into the future.
    #[prost(message, optional, tag="5")]
    pub max_clock_drift: ::core::option::Option<super::super::super::super::google::protobuf::Duration>,
    /// Block height when the client was frozen due to a misbehaviour
    #[prost(message, optional, tag="6")]
    pub frozen_height: ::core::option::Option<super::super::super::core::client::v1::Height>,
    /// Latest height the client was updated to
    #[prost(message, optional, tag="7")]
    pub latest_height: ::core::option::Option<super::super::super::core::client::v1::Height>,
    /// Proof specifications used in verifying counterparty state
    #[prost(message, repeated, tag="8")]
    pub proof_specs: ::prost::alloc::vec::Vec<super::super::super::super::ics23::ProofSpec>,
    /// Path at which next upgraded client will be committed.
    /// Each element corresponds to the key for a single CommitmentProof in the
    /// chained proof. NOTE: ClientState must stored under
    /// `{upgradePath}/{upgradeHeight}/clientState` ConsensusState must be stored
    /// under `{upgradepath}/{upgradeHeight}/consensusState` For SDK chains using
    /// the default upgrade module, upgrade_path should be []string{"upgrade",
    /// "upgradedIBCState"}`
    #[prost(string, repeated, tag="9")]
    pub upgrade_path: ::prost::alloc::vec::Vec<::prost::alloc::string::String>,
    /// This flag, when set to true, will allow governance to recover a client
    /// which has expired
    #[prost(bool, tag="10")]
    pub allow_update_after_expiry: bool,
    /// This flag, when set to true, will allow governance to unfreeze a client
    /// whose chain has experienced a misbehaviour event
    #[prost(bool, tag="11")]
    pub allow_update_after_misbehaviour: bool,
}
/// ConsensusState defines the consensus state from Tendermint.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ConsensusState {
    /// timestamp that corresponds to the block height in which the ConsensusState
    /// was stored.
    #[prost(message, optional, tag="1")]
    pub timestamp: ::core::option::Option<super::super::super::super::google::protobuf::Timestamp>,
    /// commitment root (i.e app hash)
    #[prost(message, optional, tag="2")]
    pub root: ::core::option::Option<super::super::super::core::commitment::v1::MerkleRoot>,
    #[prost(bytes="vec", tag="3")]
    pub next_validators_hash: ::prost::alloc::vec::Vec<u8>,
}
/// Misbehaviour is a wrapper over two conflicting Headers
/// that implements Misbehaviour interface expected by ICS-02
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Misbehaviour {
    #[prost(string, tag="1")]
    pub client_id: ::prost::alloc::string::String,
    #[prost(message, optional, tag="2")]
    pub header_1: ::core::option::Option<Header>,
    #[prost(message, optional, tag="3")]
    pub header_2: ::core::option::Option<Header>,
}
/// Header defines the Tendermint client consensus Header.
/// It encapsulates all the information necessary to update from a trusted
/// Tendermint ConsensusState. The inclusion of TrustedHeight and
/// TrustedValidators allows this update to process correctly, so long as the
/// ConsensusState for the TrustedHeight exists, this removes race conditions
/// among relayers The SignedHeader and ValidatorSet are the new untrusted update
/// fields for the client. The TrustedHeight is the height of a stored
/// ConsensusState on the client that will be used to verify the new untrusted
/// header. The Trusted ConsensusState must be within the unbonding period of
/// current time in order to correctly verify, and the TrustedValidators must
/// hash to TrustedConsensusState.NextValidatorsHash since that is the last
/// trusted validator set at the TrustedHeight.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Header {
    #[prost(message, optional, tag="1")]
    pub signed_header: ::core::option::Option<::tendermint_proto::types::SignedHeader>,
    #[prost(message, optional, tag="2")]
    pub validator_set: ::core::option::Option<::tendermint_proto::types::ValidatorSet>,
    #[prost(message, optional, tag="3")]
    pub trusted_height: ::core::option::Option<super::super::super::core::client::v1::Height>,
    #[prost(message, optional, tag="4")]
    pub trusted_validators: ::core::option::Option<::tendermint_proto::types::ValidatorSet>,
}
/// Fraction defines the protobuf message type for tmmath.Fraction that only
/// supports positive values.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Fraction {
    #[prost(uint64, tag="1")]
    pub numerator: u64,
    #[prost(uint64, tag="2")]
    pub denominator: u64,
}
