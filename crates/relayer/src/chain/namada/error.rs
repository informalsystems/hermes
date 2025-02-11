use flex_error::{define_error, DisplayOnly, TraceError};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use tendermint::Error as TendermintError;
use tendermint_proto::Error as TendermintProtoError;
use tendermint_rpc::Error as TendermintRpcError;

define_error! {
    Error {
        AddressDecode
            { raw: String }
            |e| { format!("Namada address decoding failed for {}", e.raw) },

        DenomNotFound
            { denom: String }
            |e| { format!("No denom for {}", e.denom) },

        Namada
            [ TraceError<namada_sdk::error::Error> ]
            |_| { "Namada error" },

        Rpc
            { url: tendermint_rpc::Url }
            [ TendermintRpcError ]
            |e| { format!("RPC error to endpoint {}", e.url) },

        HealthCheckJsonRpc
            {
                chain_id: ChainId,
                address: String,
                endpoint: String,
            }
            [ DisplayOnly<TendermintRpcError> ]
            |e| {
                format!("health check failed for endpoint {0} on the JSON-RPC interface of chain {1}:{2}",
                    e.endpoint, e.chain_id, e.address)
            },

        InvalidHeight
            [ TendermintError ]
            |_| { "invalid height" },

        Decode
            [ TendermintProtoError ]
            |_| { "error decoding protobuf" },

        Query
            [ TraceError<namada_sdk::queries::Error> ]
            |_| { "Query error" },

        BorshDecode
            [ TraceError<std::io::Error> ]
            |_| { "borsh decoding failed" },

        DryRun
            { tx_result: namada_sdk::tx::data::TxResult<String> }
            |e| { format!("Dry run to simulate a transaction failed: {:?}", e.tx_result) },

        Upgrade
            |_| { "Namada doesn't support `MsgIbcSoftwareUpgrade` and `UpgradeProposal`" },

        Version
            { version: String }
            |e| { format!("Parsing the version string failed: {}", e.version) },
    }
}

impl From<Error> for crate::error::Error {
    fn from(error: Error) -> Self {
        Self::namada(error)
    }
}
