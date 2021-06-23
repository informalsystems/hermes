use flex_error::define_error;
use tendermint::abci::Code;
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
        2 => light_client_already_exists_error(),
        3 => invalid_light_client_error(),
        4 => light_client_not_found_error(),
        5 => frozen_light_client_error(),
        6 => invalid_client_metadata_error(),
        7 => consensus_state_not_found_error(),
        8 => invalid_consensus_state_error(),
        9 => client_type_not_found_error(),
        10 => invalid_client_type_error(),
        11 => commitment_root_not_found_error(),
        12 => invalid_client_header_error(),
        13 => invalid_light_client_misbehavior_error(),
        14 => client_state_verification_failed_error(),
        15 => client_consensus_state_verification_failed_error(),
        16 => connection_state_verification_failed_error(),
        17 => client_state_verification_failed_error(),
        18 => packet_commitment_verification_failed_error(),
        19 => packet_acknowledgement_verification_failed_error(),
        20 => packet_receipt_verification_failed_error(),
        21 => next_sequence_receive_verification_failed_error(),
        22 => self_consensus_state_not_found_error(),
        23 => update_light_client_failed_error(),
        24 => invalid_update_client_proposal_error(),
        25 => invalid_client_upgrade_error(),
        26 => invalid_height_error(),
        27 => invalid_client_state_substitute_error(),
        28 => invalid_upgrade_proposal_error(),
        29 => inactive_client_error(),
        _ => unknown_client_error(code),
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
        Code::Ok => unexpected_ok_error(),
        Code::Err(code) => {
            let codespace = result.codespace.to_string();
            if codespace == "client" {
                client_error(client_error_from_code(code))
            } else {
                // TODO: Implement mapping for other codespaces in ibc-go
                unknown_sdk_error(code)
            }
        }
    }
}
