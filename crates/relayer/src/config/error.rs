use flex_error::{define_error, TraceError};

define_error! {
    Error {
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
    }
}
