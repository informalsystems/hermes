use flex_error::{define_error, TraceError};
use ic_agent::AgentError;

define_error! {
    VpError {
        AgentError
            [TraceError<AgentError>]
            |_| { "vp agent error" },

        CustomError
            { reason: String }
            | e | { format!("Custom error: ({})", e.reason ) },

        DecodeIcTypeError
            [ TraceError<candid::Error>]
            | _ | { "decode ic type error" },

        PrincipalError
            [ TraceError<ic_agent::export::PrincipalError> ]
            | _ | { "build principal error"},

        CreateIdentityError
            [ TraceError<ic_agent::identity::PemError>]
            | _ | { "create identity failed" },
    }
}
