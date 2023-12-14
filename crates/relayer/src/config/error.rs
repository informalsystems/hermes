use flex_error::{
    define_error,
    TraceError,
};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
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

            Io
            [ TraceError<std::io::Error> ]
            |_| { "config I/O error" },

        Decode
            [ TraceError<toml::de::Error> ]
            |_| { "invalid configuration" },

        InvalidCompatMode
            { compat_mode: String, valide_modes: &'static str }
            |e| { format!("invalid compatibility mode: '{}' (supported: {})", e.compat_mode, e.valide_modes) },

        Encode
            [ TraceError<toml::ser::Error> ]
            |_| { "invalid configuration" },

        WrongType
            |_| { "wrong configuration type" },

        InvalidGasPrice
            { price: String }
        |e| {
            format!("invalid gas price: {}", e.price)
        },

        CosmosConfigError { reason: String }
        |e| {
            format!("invalid cosmos config: {}", e.reason)
        },
    }
}
