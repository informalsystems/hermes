use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use tendermint_light_client_verifier::types::TrustThreshold;

use flex_error::{define_error, TraceError};
use tracing_subscriber::filter::ParseError;

// Specifies all the possible errors that a Hermes config file can contain.
define_error! {
    Error {
        ZeroChain
            |_| { "config file does not specify any chain" },

        InvalidLogDirective
            { directive: String, }
            [ TraceError<ParseError> ]
            |e| {
                format!("invalid log directive: {0:?}", e.directive)
            },

        InvalidMode
            { reason: String, }
            |e| {
                format!("config file specifies invalid mode config, caused by: {0}",
                    e.reason)
            },

        DuplicateChains
            { chain_id: ChainId }
            |e| {
                format!("config file has duplicate entry for the chain '{0}'",
                    e.chain_id)
            },

        InvalidTrustThreshold
            {
                threshold: TrustThreshold,
                chain_id: ChainId,
                reason: String
            }
            |e| {
                format!("config file specifies an invalid `trust_threshold` ({0}) for the chain '{1}', caused by: {2}",
                    e.threshold, e.chain_id, e.reason)
            },

        DeprecatedGasAdjustment
            {
                gas_adjustment: f64,
                gas_multiplier: f64,
                chain_id: ChainId,
            }
            |e| {
                format!(
                    "config file specifies deprecated setting `gas_adjustment = {1}` for the chain '{0}'; \
                    to get the same behavior, use `gas_multiplier = {2}",
                    e.chain_id, e.gas_adjustment, e.gas_multiplier
                )
            },
            Io
            [ TraceError<std::io::Error> ]
            |_| { "config I/O error" },

        Decode
            [ TraceError<toml::de::Error> ]
            |_| { "invalid configuration" },

        Encode
            [ TraceError<toml::ser::Error> ]
            |_| { "invalid configuration" },

        InvalidGasPrice
            { price: String }
            |e| { format!("invalid gas price: {}", e.price) },

        WrongType
            |_| { "wrong configuration type" },
    }
}
