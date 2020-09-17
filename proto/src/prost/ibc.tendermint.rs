/// ClientState from Tendermint tracks the current validator set, latest height,
/// and a possible frozen height.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ClientState {
    #[prost(string, tag="1")]
    pub chain_id: std::string::String,
    #[prost(message, optional, tag="2")]
    pub trust_level: ::std::option::Option<Fraction>,
    /// duration of the period since the LastestTimestamp during which the
    /// submitted headers are valid for upgrade
    #[prost(message, optional, tag="3")]
    pub trusting_period: ::std::option::Option<::prost_types::Duration>,
    /// duration of the staking unbonding period
    #[prost(message, optional, tag="4")]
    pub unbonding_period: ::std::option::Option<::prost_types::Duration>,
    /// defines how much new (untrusted) header's Time can drift into the future.
    #[prost(message, optional, tag="5")]
    pub max_clock_drift: ::std::option::Option<::prost_types::Duration>,
    /// Block height when the client was frozen due to a misbehaviour
    #[prost(message, optional, tag="6")]
    pub frozen_height: ::std::option::Option<super::client::Height>,
    /// Latest height the client was updated to
    #[prost(message, optional, tag="7")]
    pub latest_height: ::std::option::Option<super::client::Height>,
    /// Proof specifications used in verifying counterparty state
    #[prost(message, repeated, tag="8")]
    pub proof_specs: ::std::vec::Vec<super::super::ics23::ProofSpec>,
}
/// ConsensusState defines the consensus state from Tendermint.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ConsensusState {
    /// timestamp that corresponds to the block height in which the ConsensusState
    /// was stored.
    #[prost(message, optional, tag="1")]
    pub timestamp: ::std::option::Option<::prost_types::Timestamp>,
    /// commitment root (i.e app hash)
    #[prost(message, optional, tag="2")]
    pub root: ::std::option::Option<super::commitment::MerkleRoot>,
    /// height at which the consensus state was stored.
    #[prost(message, optional, tag="3")]
    pub height: ::std::option::Option<super::client::Height>,
    #[prost(bytes, tag="4")]
    pub next_validators_hash: std::vec::Vec<u8>,
}
/// Misbehaviour is a wrapper over two conflicting Headers
/// that implements Misbehaviour interface expected by ICS-02
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Misbehaviour {
    #[prost(string, tag="1")]
    pub client_id: std::string::String,
    #[prost(string, tag="2")]
    pub chain_id: std::string::String,
    #[prost(message, optional, tag="3")]
    pub header_1: ::std::option::Option<Header>,
    #[prost(message, optional, tag="4")]
    pub header_2: ::std::option::Option<Header>,
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
    pub signed_header: ::std::option::Option<super::super::tendermint::types::SignedHeader>,
    #[prost(message, optional, tag="2")]
    pub validator_set: ::std::option::Option<super::super::tendermint::types::ValidatorSet>,
    #[prost(message, optional, tag="3")]
    pub trusted_height: ::std::option::Option<super::client::Height>,
    #[prost(message, optional, tag="4")]
    pub trusted_validators: ::std::option::Option<super::super::tendermint::types::ValidatorSet>,
}
/// Fraction defines the protobuf message type for tmmath.Fraction
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Fraction {
    #[prost(int64, tag="1")]
    pub numerator: i64,
    #[prost(int64, tag="2")]
    pub denominator: i64,
}
