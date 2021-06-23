use tendermint::abci::Code;
use tendermint_rpc::endpoint::broadcast::tx_commit::TxResult;
use thiserror::Error;

// Provides mapping for errors returned from ibc-go and cosmos-sdk
#[derive(Clone, Debug, Error)]
pub enum SdkError {
    #[error("ICS02 Client Error: {0}")]
    Client(ClientError),

    #[error("Unknown SDK Error")]
    Unknown,
}

#[derive(Clone, Debug, Error)]
pub enum ClientError {
    #[error("light client already exists")]
    LightClientAlreadyExists,

    #[error("light client is invalid")]
    InvalidLightClient,

    #[error("light client not found")]
    LightClientNotFound,

    #[error("light client is frozen due to misbehaviour")]
    FrozenLightClient,

    #[error("invalid client metadata")]
    InvalidClientMetadata,

    #[error("consensus state not found")]
    ConsensusStateNotFound,

    #[error("invalid consensus state")]
    InvalidConsensusState,

    #[error("client type not found")]
    ClientTypeNotFound,

    #[error("invalid client type")]
    InvalidClientType,

    #[error("commitment root not found")]
    CommitmentRootNotFound,

    #[error("invalid client header")]
    InvalidClientHeader,

    #[error("invalid light client misbehaviour")]
    InvalidLightClientMisbehavior,

    #[error("client state verification failed")]
    ClientStateVerificationFailed,

    #[error("client consensus state verification failed")]
    ClientConsensusStateVerificationFailed,

    #[error("connection state verification failed")]
    ConnectionStateVerificationFailed,

    #[error("channel state verification failed")]
    ChannelStateVerificationFailed,

    #[error("packet commitment verification failed")]
    PacketCommitmentVerificationFailed,

    #[error("packet acknowledgement verification failed")]
    PacketAcknowledgementVerificationFailed,

    #[error("packet receipt verification failed")]
    PacketReceiptVerificationFailed,

    #[error("next sequence receive verification failed")]
    NextSequenceReceiveVerificationFailed,

    #[error("self consensus state not found")]
    SelfConsensusStateNotFound,

    #[error("unable to update light client")]
    UpdateLightClientFailed,

    #[error("invalid update client proposal")]
    InvalidUpdateClientProposal,

    #[error("invalid client upgrade")]
    InvalidClientUpgrade,

    #[error("invalid height")]
    InvalidHeight,

    #[error("invalid client state substitute")]
    InvalidClientStateSubstitute,

    #[error("invalid upgrade proposal")]
    InvalidUpgradeProposal,

    #[error("client is not active")]
    InactiveClient,

    #[error("Unknown client error")]
    Unknown,
}

impl ClientError {
    // The error code mapping follows the Go code at
    // ibc-go/modules/core/02-client/types/errors.go
    fn from_code(code: u32) -> ClientError {
        match code {
            2 => ClientError::LightClientAlreadyExists,
            3 => ClientError::InvalidLightClient,
            4 => ClientError::LightClientNotFound,
            5 => ClientError::FrozenLightClient,
            6 => ClientError::InvalidClientMetadata,
            7 => ClientError::ConsensusStateNotFound,
            8 => ClientError::InvalidConsensusState,
            9 => ClientError::ClientTypeNotFound,
            10 => ClientError::InvalidClientType,
            11 => ClientError::CommitmentRootNotFound,
            12 => ClientError::InvalidClientHeader,
            13 => ClientError::InvalidLightClientMisbehavior,
            14 => ClientError::ClientStateVerificationFailed,
            15 => ClientError::ClientConsensusStateVerificationFailed,
            16 => ClientError::ConnectionStateVerificationFailed,
            17 => ClientError::ChannelStateVerificationFailed,
            18 => ClientError::PacketCommitmentVerificationFailed,
            19 => ClientError::PacketAcknowledgementVerificationFailed,
            20 => ClientError::PacketReceiptVerificationFailed,
            21 => ClientError::NextSequenceReceiveVerificationFailed,
            22 => ClientError::SelfConsensusStateNotFound,
            23 => ClientError::UpdateLightClientFailed,
            24 => ClientError::InvalidUpdateClientProposal,
            25 => ClientError::InvalidClientUpgrade,
            26 => ClientError::InvalidHeight,
            27 => ClientError::InvalidClientStateSubstitute,
            28 => ClientError::InvalidUpgradeProposal,
            29 => ClientError::InactiveClient,
            _ => ClientError::Unknown,
        }
    }
}

// Converts the error in a TxResult into SdkError with the same
// mapping as defined in ibc-go and cosmos-sdk. This assumes the
// target chain we are interacting with are using cosmos-sdk and ibc-go.
//
// TODO: investigate ways to automatically generate the mapping by parsing
// the errors.go source code directly
pub fn sdk_error_from_tx_result(result: &TxResult) -> SdkError {
    match result.code {
        Code::Ok => SdkError::Unknown,
        Code::Err(code) => {
            let codespace = result.codespace.to_string();
            if codespace == "client" {
                SdkError::Client(ClientError::from_code(code))
            } else {
                // TODO: Implement mapping for other codespaces in ibc-go
                SdkError::Unknown
            }
        }
    }
}
