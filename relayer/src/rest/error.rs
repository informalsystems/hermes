use flex_error::define_error;
use serde::Serialize;

use ibc::{ics24_host::error::ValidationError, ics24_host::identifier::ChainId};

define_error! {
    #[derive(Debug, Serialize)]
    RestApiError {
        ChannelSend
            { cause: String }
            |e| { format!("failed to send a request through crossbeam channel: {0}", e.cause) },

        ChannelRecv
            { cause: String }
            |e| { format!("failed to receive a reply from crossbeam channel: {0}", e.cause) },

        Serialization
            { cause: String }
            |e| { format!("failed while serializing reply into json value: {0}", e.cause) },

        ChainConfigNotFound
            { chain_id: ChainId }
            |e| { format!("could not find configuration for chain id {0}", e.chain_id) },

        InvalidChainId
            { chain_id_raw: String }
            [ ValidationError ]
            |e| { format!("failed to parse the string {0} into a valid chain identifier", e.chain_id_raw) },

        InvalidChainConfig
            { cause: String }
            |e| { format!("failed while parsing the request body into a chain configuration {}", e.cause) },

        Unimplemented
            | _ | { "not implemented".to_string() },
    }
}
