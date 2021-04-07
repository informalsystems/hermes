//! Custom-made solution to output a JSON return message and ensure a return code
//! from a CLI command. The main use-case for this module is to provide a consistent output for
//! queries and transactions.
//!
//! The examples below rely on crate-private methods (for this reason, doctests are ignored).
//! They are intended for contributors to crate `relayer-cli`, and _not_ for users of this binary.
//!
//! ## Examples on how to use the quick-access constructors:
//!
//! - Exit from a query/tx with a `String` error:
//!
//! ```ignore
//! let e = String::from("error message");
//! Output::error(e).exit();
//! // or as an alternative:
//! Output::error(json!("error occurred")).exit();
//! ```
//!
//! - Exit from a query/tx with an error of type `anomaly`:
//! In the case where the error is a complex type such as anomaly (including backtraces), it is
//! better to simplify the output and only write out the chain of error sources, which we can
//! achieve with `format!("{}", e)`. The complete solution is as follows:
//!
//! ```ignore
//! let e: Error = Kind::Query.into();
//! Output::error(format!("{}", e)).exit();
//! ```
//!
//! #### Note:
//! The resulting output that this approach generates is determined by the 'error' annotation given
//! to the error object `Kind::Query`. If this error object comprises any positional arguments,
//! e.g. as achieved by `Query(String, String)`, then it is important to cover these arguments
//! in the `error` annotation, for instance:
//! ```ignore
//! #[derive(Debug, Error)]
//! pub enum Kind {
//!     #[error("failed with underlying causes: {0}, {1}")]
//!     Query(String, String),
//!     // ...
//! }
//! ```
//!
//! - Exit from a query/tx with success:
//!
//! ```ignore
//! let cs = ChannelEnd::default();
//! Output::success(cs).exit();
//! ```
//!
//! - Exit from a query/tx with success and multiple objects in the result:
//!
//! ```ignore
//! let h = Height::default();
//! let end = ConnectionEnd::default();
//! Output::success(h).with_result(end).exit();
//! ```

use std::fmt;

use serde::Serialize;
use tracing::error;

use crate::components::TRACING_COMPONENT_ID;
use crate::prelude::{app_reader, Application};

/// Functional-style method to exit a program.
///
/// ## Note: See `Output::exit()` for the preferred method of exiting a relayer command.
pub fn exit_with(out: Output) {
    // Handle the output message
    match json() {
        true => println!("{}", serde_json::to_string(&out).unwrap()),
        false => println!("{}\n{:#}", out.status, out.result),
    }

    // The return code
    if out.status == Status::Error {
        std::process::exit(1);
    } else {
        std::process::exit(0);
    }
}

/// Returns true if the application global json flag `-j` or `--json` is enabled.
/// Returns false otherwise.
pub fn json() -> bool {
    let a = app_reader();
    // if the custom Tracing component is loaded, then JSON is enabled
    a.state()
        .components
        .get_by_id(TRACING_COMPONENT_ID)
        .is_some()
}

/// Exits the program. Useful when a type produces an error which can no longer be propagated, and
/// the program must exit instead.
///
/// ## Example of use
/// - Without this function:
/// ```ignore
/// let res = ForeignClient::new(chains.src.clone(), chains.dst.clone());
/// let client = match res {
///     Ok(client) => client,
///     Err(e) => return Output::error(format!("{}", e)).exit(),
/// };
/// ```
/// - With support from `exit_with_unrecoverable_error`:
/// ```ignore
/// let client_a = ForeignClient::new(chains.src.clone(), chains.dst.clone())
///     .unwrap_or_else(exit_with_unrecoverable_error);
/// ```
pub fn exit_with_unrecoverable_error<T, E: fmt::Display>(err: E) -> T {
    // TODO(@romac): Once never (!) stabilizes, adapt `Output::exit` to return !
    //  https://github.com/informalsystems/ibc-rs/pull/688#discussion_r583758439
    Output::error(format!("{}", err)).exit();
    unreachable!()
}

/// A CLI output with support for JSON serialization. The only mandatory field is the `status`,
/// which typically signals a success (UNIX process return code `0`) or an error (code `1`). An
/// optional `result` can be added to an output.
///
#[derive(Serialize, Debug)]
pub struct Output {
    /// The return status
    pub status: Status,

    /// The result of a command, such as the output from a query or transaction.
    pub result: serde_json::Value,
}

impl Output {
    /// Constructs a new `Output` with the provided `status` and an empty `result`.
    pub fn new(status: Status) -> Self {
        Output {
            status,
            result: serde_json::Value::Null,
        }
    }

    /// Constructor that returns a new `Output` having a `Success` status and empty `result`.
    pub fn with_success() -> Self {
        Output::new(Status::Success)
    }

    /// Constructor that returns a new `Output` having an `Error` status and empty `result`.
    pub fn with_error() -> Self {
        Output::new(Status::Error)
    }

    /// Builder-style method for attaching a result to an output object.
    pub fn with_result(mut self, result: impl Serialize + std::fmt::Debug) -> Self {
        self.result = Self::serialize_result(result);
        self
    }

    /// Quick-access constructor for an output signalling a success `status` and tagged with the
    /// input `result`.
    pub fn success(result: impl Serialize + std::fmt::Debug) -> Self {
        Output::with_success().with_result(result)
    }

    /// Quick-access constructor for an output signalling a error `status` and tagged with the
    /// input `result`.
    pub fn error(result: impl Serialize + std::fmt::Debug) -> Self {
        Output::with_error().with_result(result)
    }

    /// Helper to serialize a result into a `serde_json::Value`.
    fn serialize_result(res: impl Serialize + std::fmt::Debug) -> serde_json::Value {
        let last_resort = format!("{:?}", res);

        match serde_json::to_value(res) {
            Ok(json_val) => json_val,
            Err(e) => {
                // Signal the serialization error
                error!(
                    "Output constructor failed with non-recoverable error {} for input {}",
                    e, last_resort
                );
                // Package the result with the infallible `Debug` instead of `JSON`
                serde_json::Value::String(last_resort)
            }
        }
    }

    /// Exits from the process with the current output. Convenience wrapper over `exit_with`.
    pub fn exit(self) {
        exit_with(self);
    }
}

/// Represents the exit status of any CLI command
#[derive(Serialize, Debug, PartialEq, Eq)]
pub enum Status {
    #[serde(rename(serialize = "success"))]
    Success,

    #[serde(rename(serialize = "error"))]
    Error,
}

impl fmt::Display for Status {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Status::Success => write!(f, "Success"),
            Status::Error => write!(f, "Error"),
        }
    }
}
