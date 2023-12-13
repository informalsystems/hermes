use candid::CandidType;
use flex_error::{define_error, TraceError};
use ic_agent::AgentError;
use serde::Deserialize;
use thiserror::Error;

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

#[derive(CandidType, Deserialize, Debug, Error)]
pub enum VerificationProxiesError {
    #[error("client has been created")]
    ClientHasBeenCreated,
    #[error("connection has been created")]
    ConnectionHasBeenCreated,
    #[error("channel has been created: `{0}`")]
    ChannelHasBeenCreated(String),
    #[error("client state not found: `{0}`")]
    ClientStateNotFound(String),
    #[error("consensus state not found: `{0}`")]
    ConsensusStateNotFound(String),
    #[error("unknown any message")]
    UnknownAnyMessage,
    #[error("the message is malformed and cannot be decoded error")]
    MalformedMessageBytes,
    #[error("unauthorized")]
    Unauthorized,
    #[error("custom error: (`{0}`)")]
    CustomError(String),
}
