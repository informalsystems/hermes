//! The BroadcastError is used by the telemetry in order to correctly batch
//! together the error reports from ibc-go or Cosmos SDK.
//! When a broadcast error is received by Hermes it will contain a code and
//! a description, but the code description depends on the source of the error.
//! For example Cosmos SDK error code 13 is "insufficient fee", and error
//! code 13 for Ibc Go is "invalid packet".
//! The description might contain some variables for example error 32 would be:
//! "account sequence mismatch, expected 1234, got 1235: incorrect account sequence"
//! The BroadcastError will reduce the description to simple: "incorrect account sequence"
//!
//! Cosmos SDK errors: <https://github.com/cosmos/cosmos-sdk/blob/v0.50.1/types/errors/errors.go>
//! Ibc Go errors: <https://github.com/cosmos/ibc-go/blob/v8.0.0/modules/core/04-channel/types/errors.go>

pub struct BroadcastError {
    pub code: u32,
    pub description: String,
}

impl BroadcastError {
    pub fn new(code: u32, description: &str) -> Self {
        let short_description = get_short_description(code, description);
        Self {
            code,
            description: short_description,
        }
    }
}

fn get_short_description(code: u32, description: &str) -> String {
    match code {
        2 => {
            let sdk_error = "tx parse error";
            let ibc_go_error = "channel already exists";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        3 => {
            let sdk_error = "invalid sequence";
            let ibc_go_error = "channel not found";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        4 => {
            let sdk_error = "unauthorized";
            let ibc_go_error = "invalid channel";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        5 => {
            let sdk_error = "insufficient funds";
            let ibc_go_error = "invalid channel state";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        6 => {
            let sdk_error = "unknown request";
            let ibc_go_error = "invalid channel ordering";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        7 => {
            let sdk_error = "invalid address";
            let ibc_go_error = "invalid counterparty channel";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        8 => {
            let sdk_error = "invalid pubkey";
            let ibc_go_error = "invalid channel capability";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        9 => {
            let sdk_error = "unknown address";
            let ibc_go_error = "channel capability not found";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        10 => {
            let sdk_error = "invalid coins";
            let ibc_go_error = "sequence send not found";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        11 => {
            let sdk_error = "out of gas";
            let ibc_go_error = "sequence receive not found";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        12 => {
            let sdk_error = "memo too large";
            let ibc_go_error = "sequence acknowledgement not found";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        13 => {
            let sdk_error = "insufficient fee";
            let ibc_go_error = "invalid packet";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        14 => {
            let sdk_error = "maximum number of signatures exceeded";
            let ibc_go_error = "packet timeout";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        15 => {
            let sdk_error = "no signatures supplied";
            let ibc_go_error = "too many connection hops";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        16 => {
            let sdk_error = "failed to marshal JSON bytes";
            let ibc_go_error = "invalid acknowledgement";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        17 => {
            let sdk_error = "failed to unmarshal JSON bytes";
            let ibc_go_error = "acknowledgement for packet already exists";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        18 => {
            let sdk_error = "invalid request";
            let ibc_go_error = "invalid channel identifier";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        19 => {
            let sdk_error = "tx already in mempool";
            let ibc_go_error = "packet already received";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        20 => {
            let sdk_error = "mempool is full";
            let ibc_go_error = "packet commitment not found";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        21 => {
            let sdk_error = "tx too large";
            let ibc_go_error = "packet sequence is out of order";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        22 => {
            let sdk_error = "key not found";
            let ibc_go_error = "packet messages are redundant";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        23 => {
            let sdk_error = "invalid account password";
            let ibc_go_error = "message is redundant, no-op will be performed";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        24 => {
            let sdk_error = "tx intended signer does not match the given signer";
            let ibc_go_error = "invalid channel version";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        25 => {
            let sdk_error = "invalid gas adjustment";
            let ibc_go_error = "packet has not been sent";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        26 => {
            let sdk_error = "invalid height";
            let ibc_go_error = "invalid packet timeout";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else if description.contains(ibc_go_error) {
                Some(ibc_go_error.to_owned())
            } else {
                None
            }
        }
        27 => {
            let sdk_error = "invalid version";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        28 => {
            let sdk_error = "invalid chain-id";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        29 => {
            let sdk_error = "invalid type";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        30 => {
            let sdk_error = "tx timeout height";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        31 => {
            let sdk_error = "unknown extension options";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        32 => {
            let sdk_error = "incorrect account sequence";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        33 => {
            let sdk_error = "failed packing protobuf message to Any";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        34 => {
            let sdk_error = "failed unpacking protobuf message from Any";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        35 => {
            let sdk_error = "internal logic error";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        36 => {
            let sdk_error = "conflict";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        37 => {
            let sdk_error = "feature not supported";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        38 => {
            let sdk_error = "not found";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        39 => {
            let sdk_error = "Internal IO error";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        40 => {
            let sdk_error = "error in app.toml";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        41 => {
            let sdk_error = "invalid gas limit";
            if description.contains(sdk_error) {
                Some(sdk_error.to_owned())
            } else {
                None
            }
        }
        _ => None,
    }
    .unwrap_or_else(|| "unknown error".to_owned())
}
