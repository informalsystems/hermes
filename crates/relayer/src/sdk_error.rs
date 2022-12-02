use flex_error::define_error;
use tendermint::abci::Code;

// Provides mapping for errors returned from ibc-go and cosmos-sdk
define_error! {
    SdkError {
        Client
            [ ClientError ]
            |_| { "ICS02 Client Error" },

        UnexpectedOk
            |_| { "expected error code, instead got Ok" },

        UnknownSdk
            {
                codespace: String,
                code: u32,
            }
            | e | {
                format_args!("unknown SDK error with code space: {}, code: {}", e.codespace, e.code)
            },

        UnknownTxSync
            { code: u32 }
            | e | { format_args!("unknown TX sync response error: {}", e.code) },

        OutOfGas
            { code: u32 }
            |_| { "the gas requirement is higher than the configured maximum gas! please check the Hermes config.toml".to_string() },

        InsufficientFee
            { code: u32 }
            |_| { "the price configuration for this chain may be too low! please check the `gas_price.price` Hermes config.toml".to_string() },
    }
}

define_error! {
    ClientError {
        LightClientAlreadyExists
            |_| { "light client already exists" },

        InvalidLightClient
            |_| { "light client is invalid" },

        LightClientNotFound
            |_| { "light client not found" },

        FrozenLightClient
            |_| { "light client is frozen due to misbehaviour" },

        InvalidClientMetadata
            |_| { "invalid client metadata" },

        ConsensusStateNotFound
            |_| { "consensus state not found" },

        InvalidConsensusState
            |_| { "invalid consensus state" },

        ClientTypeNotFound
            |_| { "client type not found" },

        InvalidClientType
            |_| { "invalid client type" },

        CommitmentRootNotFound
            |_| { "commitment root not found" },

        InvalidClientHeader
            |_| { "invalid client header" },

        InvalidLightClientMisbehavior
            |_| { "invalid light client misbehaviour" },

        ClientStateVerificationFailed
            |_| { "client state verification failed" },

        ClientConsensusStateVerificationFailed
            |_| { "client consensus state verification failed" },

        ConnectionStateVerificationFailed
            |_| { "connection state verification failed" },

        ChannelStateVerificationFailed
            |_| { "channel state verification failed" },

        PacketCommitmentVerificationFailed
            |_| { "packet commitment verification failed" },

        PacketAcknowledgementVerificationFailed
            |_| { "packet acknowledgement verification failed" },

        PacketReceiptVerificationFailed
            |_| { "packet receipt verification failed" },

        NextSequenceReceiveVerificationFailed
            |_| { "next sequence receive verification failed" },

        SelfConsensusStateNotFound
            |_| { "self consensus state not found" },

        UpdateLightClientFailed
            |_| { "unable to update light client" },

        InvalidUpdateClientProposal
            |_| { "invalid update client proposal" },

        InvalidClientUpgrade
            |_| { "invalid client upgrade" },

        InvalidHeight
            |_| { "invalid height" },

        InvalidClientStateSubstitute
            |_| { "invalid client state substitute" },

        InvalidUpgradeProposal
            |_| { "invalid upgrade proposal" },

        InactiveClient
            |_| { "client is not active" },

        UnknownClient
            { code: u32 }
            |e| { format!("unknown client error: {}", e.code) },
    }
}

// The error code mapping follows the Go code at
// ibc-go/modules/core/02-client/types/errors.go
fn client_error_from_code(code: u32) -> ClientError {
    match code {
        2 => ClientError::light_client_already_exists(),
        3 => ClientError::invalid_light_client(),
        4 => ClientError::light_client_not_found(),
        5 => ClientError::frozen_light_client(),
        6 => ClientError::invalid_client_metadata(),
        7 => ClientError::consensus_state_not_found(),
        8 => ClientError::invalid_consensus_state(),
        9 => ClientError::client_type_not_found(),
        10 => ClientError::invalid_client_type(),
        11 => ClientError::commitment_root_not_found(),
        12 => ClientError::invalid_client_header(),
        13 => ClientError::invalid_light_client_misbehavior(),
        14 => ClientError::client_state_verification_failed(),
        15 => ClientError::client_consensus_state_verification_failed(),
        16 => ClientError::connection_state_verification_failed(),
        17 => ClientError::client_state_verification_failed(),
        18 => ClientError::packet_commitment_verification_failed(),
        19 => ClientError::packet_acknowledgement_verification_failed(),
        20 => ClientError::packet_receipt_verification_failed(),
        21 => ClientError::next_sequence_receive_verification_failed(),
        22 => ClientError::self_consensus_state_not_found(),
        23 => ClientError::update_light_client_failed(),
        24 => ClientError::invalid_update_client_proposal(),
        25 => ClientError::invalid_client_upgrade(),
        26 => ClientError::invalid_height(),
        27 => ClientError::invalid_client_state_substitute(),
        28 => ClientError::invalid_upgrade_proposal(),
        29 => ClientError::inactive_client(),
        _ => ClientError::unknown_client(code),
    }
}

// Converts the error in a CheckTx or DeliverTx result into SdkError with the same
// mapping as defined in ibc-go and cosmos-sdk. This assumes the
// target chain we are interacting with are using cosmos-sdk and ibc-go.
//
// TODO: investigate ways to automatically generate the mapping by parsing
// the errors.go source code directly
pub fn sdk_error_from_tx_result(code: Code, codespace: &str) -> SdkError {
    match code {
        Code::Ok => SdkError::unexpected_ok(),
        Code::Err(code) => {
            if codespace == "client" {
                SdkError::client(client_error_from_code(code.into()))
            } else {
                // TODO: Implement mapping for other codespaces in ibc-go
                SdkError::unknown_sdk(codespace.to_owned(), code.into())
            }
        }
    }
}

/// Converts error codes originating from `broadcast_tx_sync` responses
/// into IBC relayer domain-type errors.
/// See [`tendermint_rpc::endpoint::broadcast::tx_sync::Response`].
/// Cf: <https://github.com/cosmos/cosmos-sdk/blob/v0.42.10/types/errors/errors.go>
pub fn sdk_error_from_tx_sync_error_code(code: u32) -> SdkError {
    match code {
        // The primary reason (we know of) causing broadcast_tx_sync to fail
        // is due to "out of gas" errors. These are unrecoverable at the moment
        // on Hermes side. We'll inform the user to check for misconfiguration.
        11 => SdkError::out_of_gas(code),
        13 => SdkError::insufficient_fee(code),
        _ => SdkError::unknown_tx_sync(code),
    }
}
