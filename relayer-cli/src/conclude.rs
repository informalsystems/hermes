//! Custom-made solution to output a JSON return message and ensure a return code
//! from a CLI command.

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
    /// An arbitrary strongly typed JSON object.
    pub result: Option<serde_json::Value>,
}

impl Output {
    /// Constructs a new `Output`.
    pub fn new(status: Status) -> Self {
        Output {
            status,
            result: None,
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

    /// Builder-style method for attaching a result to an output object.
    pub fn with_result(self, res: serde_json::Value) -> Self {
        Output {
            result: Some(res),
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
