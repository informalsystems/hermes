use flex_error::define_error;
use tendermint_rpc::abci::Code;
use tendermint_rpc::endpoint::broadcast::tx_commit::TxResult;

// Provides mapping for errors returned from ibc-go and cosmos-sdk
define_error! {
    SdkError {
        Client
            [ ClientError ]
            |_| { "ICS02 Client Error" },

        UnexpectedOk
            |_| { "Expected error code, instead got Ok" },

        UnknownSdk
            { code: u32 }
            |e| { format!("unknown SDK error: {}", e.code) },

        OutOfGas
            { code: u32 }
            |_| { "the price configuration for this chain may be too low! please check the `gas_price.price` Hermes config.toml".to_string() },
    }
}

define_error! {
    ClientError {
        LightClientAlreadyExists
            |_| { "light client already exists" },

        InvalidLightClient
            |_| { "light client already exists" },

        LightClientNotFound
            |_| { "light client already exists" },

        FrozenLightClient
            |_| { "light client already exists" },

        InvalidClientMetadata
            |_| { "light client already exists" },

        ConsensusStateNotFound
            |_| { "light client already exists" },

        InvalidConsensusState
            |_| { "light client already exists" },

        ClientTypeNotFound
            |_| { "light client already exists" },

        InvalidClientType
            |_| { "light client already exists" },

        CommitmentRootNotFound
            |_| { "light client already exists" },

        InvalidClientHeader
            |_| { "light client already exists" },

        InvalidLightClientMisbehavior
            |_| { "light client already exists" },

        ClientStateVerificationFailed
            |_| { "light client already exists" },

        ClientConsensusStateVerificationFailed
            |_| { "light client already exists" },

        ConnectionStateVerificationFailed
            |_| { "light client already exists" },

        ChannelStateVerificationFailed
            |_| { "light client already exists" },

        PacketCommitmentVerificationFailed
            |_| { "light client already exists" },

        PacketAcknowledgementVerificationFailed
            |_| { "light client already exists" },

        PacketReceiptVerificationFailed
            |_| { "light client already exists" },

        NextSequenceReceiveVerificationFailed
            |_| { "light client already exists" },

        SelfConsensusStateNotFound
            |_| { "light client already exists" },

        UpdateLightClientFailed
            |_| { "light client already exists" },

        InvalidUpdateClientProposal
            |_| { "light client already exists" },

        InvalidClientUpgrade
            |_| { "light client already exists" },

        InvalidHeight
            |_| { "light client already exists" },

        InvalidClientStateSubstitute
            |_| { "light client already exists" },

        InvalidUpgradeProposal
            |_| { "light client already exists" },

        InactiveClient
            |_| { "light client already exists" },

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

// Converts the error in a TxResult into SdkError with the same
// mapping as defined in ibc-go and cosmos-sdk. This assumes the
// target chain we are interacting with are using cosmos-sdk and ibc-go.
//
// TODO: investigate ways to automatically generate the mapping by parsing
// the errors.go source code directly
pub fn sdk_error_from_tx_result(result: &TxResult) -> SdkError {
    match result.code {
        Code::Ok => SdkError::unexpected_ok(),
        Code::Err(code) => {
            let codespace = result.codespace.to_string();
            if codespace == "client" {
                SdkError::client(client_error_from_code(code.get()))
            } else {
                // TODO: Implement mapping for other codespaces in ibc-go
                SdkError::unknown_sdk(code.get())
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
        // on the Hermes side. We'll inform the user to check for misconfig.
        11 => SdkError::out_of_gas(code),
        _ => SdkError::unknown_sdk(code),
    }
}
