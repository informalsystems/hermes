use flex_error::{define_error, TraceError};

define_error! {
    Error {
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

        InvalidGasPrice
            { price: String }
            |e| { format!("invalid gas price: {}", e.price) },
    }
}
