//! Custom-made solution to output a JSON return message and ensure a return code
//! from a CLI command. The main use-case for this module is to provide a consistent output for
//! queries and transactions.
//!
//! ## Examples:
//!
//! - Exit from a query/tx with a string error:
//!
//! ```
//! use serde_json::json;
//! use crate::conclude::Output;
//! let e = String::from("error message");
//! Output::with_error().with_result(json!(e)).exit();
//! // or as an alternative:
//! Output::with_error().with_result(json!("error occurred")).exit();
//! ```
//!
//! - Exit from a query/tx with an error of type `anomaly`:
//! In the case where the error is a complex type such as anomaly (including backtraces), it is
//! better to simplify the output and only write out the chain of error sources, which we can
//! achieve with `format!("{}", e)`. The complete solution is as follows:
//!
//! ```
//! use crate::relayer_cli::error::{Error, Kind};
//! use Output;
//! let e: Error = Kind::Query.into();
//! Output::with_success().with_result(json!(format!("{}", e))).exit();
//! ```
//!
//! - Exit from a query/tx with success:
//!
//! ```
//! Output::with_success().with_result(json!(cs)).exit();
//! ```
//!
//! - Exit from a query/tx with success and multiple objects in the result:
//!
//! ```
//! Output::with_success().with_result(json!(cs)).exit();
//! ```

use serde::Serialize;

/// Functional-style method to exit a program.
///
/// ## Note: See `Output::exit()` for the preferred method of exiting a command.
pub fn exit_with(out: Output) {
    // Handle the output message
    println!("{}", serde_json::to_string(&out).unwrap());

    // The return code
    if out.status == Status::Error {
        std::process::exit(1);
    } else {
        std::process::exit(0);
    }
}

/// A CLI output with support for JSON serialization. The only mandatory field is the `status`,
/// which typically signals a success or an error. An optional `result` can be added to an output.
#[derive(Serialize, Debug)]
pub struct Output {
    /// The return status
    pub status: Status,

    /// The result of a command, such as the output from a query or transaction.
    /// This is a vector, possibly empty, of strongly typed JSON objects.
    pub result: Vec<serde_json::Value>,
}

impl Output {
    /// Constructs a new `Output`.
    pub fn new(status: Status) -> Self {
        Output {
            status,
            result: vec![],
        }
    }

    /// Quick-access to a constructor that returns a new `Output` having a `Success` status.
    pub fn with_success() -> Self {
        Output::new(Status::Success)
    }

    /// Quick-access to a constructor that returns a new `Output` having an `Error` status.
    pub fn with_error() -> Self {
        Output::new(Status::Error)
    }

    /// Builder-style method for attaching a result to an output object. Can be called multiple
    /// times, with each subsequent call appending the given `res` JSON object to the output.
    pub fn with_result(self, res: serde_json::Value) -> Self {
        let mut new_res = self.result.clone();
        new_res.push(res);

        Output {
            result: new_res,
            ..self
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
