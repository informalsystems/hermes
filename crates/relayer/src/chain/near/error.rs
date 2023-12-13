use crate::chain::ic::errors::VpError;
use core::num::ParseIntError;
use flex_error::{define_error, TraceError};
use ibc_relayer_types::core::ics02_client::error::Error as Ics02Error;
use near_jsonrpc_client::errors::JsonRpcError;
use near_jsonrpc_primitives::types::blocks::RpcBlockError;
use near_jsonrpc_primitives::types::changes::RpcStateChangesError;
use near_jsonrpc_primitives::types::query::RpcQueryError;
use near_jsonrpc_primitives::types::transactions::RpcTransactionError;
use std::string::FromUtf8Error;

define_error! {
    NearError {
        SerdeJsonError
            [ TraceError<serde_json::Error>]
            |_| {
                let caller = std::panic::Location::caller();
                format!("serde json failure \n{}", caller)
            },

        CustomError
            { reason: String }
            |e| {
                let caller = std::panic::Location::caller();
                format!("Custom error: {} \n{}", e.reason, caller)
            },

        RpcQueryError
            [ TraceError<JsonRpcError<RpcQueryError>> ]
            | _ | {
                let caller = std::panic::Location::caller();
                format!("near rpc query error \n{}", caller)
            },

        RpcTransactionError
            [ TraceError<JsonRpcError<RpcTransactionError>>]
            | _ | {
                let caller = std::panic::Location::caller();
                format!("near rpc transaction error \n{}", caller)
            },

        RpcBlockError
            [ TraceError<JsonRpcError<RpcBlockError>>]
            | _ | {
                let caller = std::panic::Location::caller();
                format!("near rpc block error \n{}", caller)
            },

        RpcStateChangesError
            [ TraceError<JsonRpcError<RpcStateChangesError>>]
            | _ | {
                let caller = std::panic::Location::caller();
                format!("near rpc state changes error \n{}", caller)
            },

        DeliverError
            |_| {
                let caller = std::panic::Location::caller();
                format!("near chain Deliver failed \n{}", caller)
            },

        VpDeliverError
            [ TraceError<VpError>]
            | _ | {
                let caller = std::panic::Location::caller();
                format!("call vp deliver error, \n{}", caller)
            },

        DecodeVpDeliverResultFailed
            [ TraceError<prost::DecodeError>]
            | _ | {
                let caller = std::panic::Location::caller();
                format!("decode vp deliver result failed, \n{}", caller)
            },

        BuildVpClientError
            | _ | {
                let caller = std::panic::Location::caller();
                format!("near chain bootstrap build VpClientFailed \n{}", caller)
            },

        BuildIbcHeightError
            [ TraceError<Ics02Error>]
            | _ | {
                let caller = std::panic::Location::caller();
                format!("build ibc height failed \n{}", caller)
            },

        VpError
            [ TraceError<VpError> ]
            | _ | {
                let caller = std::panic::Location::caller();
                format!("vp error \n{}", caller)
            },

        NextBpsEmpty
            | _ | {
                let caller = std::panic::Location::caller();
                format!("next bps empty \n{}", caller)
            },

        ParseIntError
            [ TraceError<ParseIntError> ]
            |_ | {
                let caller = std::panic::Location::caller();
                format!("parse int error \n{}", caller)
            },

        DecodeStringError
            [ TraceError<FromUtf8Error> ]
            | _ | {
                let caller = std::panic::Location::caller();
                format!("decode string error \n{}", caller)
            },

        BuildNearProofsFailed
            [ TraceError<std::io::Error>]
            | _ | {
                let caller = std::panic::Location::caller();
                format!("build near proofs failed \n{}", caller)
            }
    }
}
