#![allow(dead_code)]
//! Handles the return message (command output) and return code from a CLI command.
//! Most of the code here is temporary/experimental.
//! https://github.com/informalsystems/ibc-rs/issues/500 will introduce a more permanent solution.

use std::collections::HashMap;

use serde::Serialize;

pub fn on_exit(json: bool, out: CommandOutput) {
    // Handle the output message
    if json {
        println!("{}", serde_json::to_string(&out).unwrap());
    } else {
        println!("status={:?}\nmsg={:?}", out.status, out.msg);
    }

    // The return code
    if out.status == CommandStatus::Error {
        std::process::exit(1);
    } else {
        std::process::exit(0);
    }
}

/// A CLI output with support for JSON serialization.
#[derive(Serialize, Debug)]
pub struct CommandOutput {
    /// The return status
    pub status: CommandStatus,

    /// An arbitrary message accompanying the output
    pub msg: Option<String>,

    /// Additional arbitrary key/values that may be present in the output
    /// TODO: at the moment this is not used!
    #[serde(flatten)]
    pub extra: HashMap<String, String>,
}

impl CommandOutput {
    pub fn new(status: CommandStatus) -> Self {
        CommandOutput {
            status,
            msg: None,
            extra: Default::default(),
        }
    }

    pub fn with_msg(self, msg: String) -> Self {
        CommandOutput {
            msg: Some(msg),
            ..self
        }
    }

    pub fn with_extra(self, k: String, v: String) -> Self {
        let mut extra = self.extra.clone();
        extra.insert(k, v);

        CommandOutput { extra, ..self }
    }
}

#[derive(Serialize, Debug, PartialEq, Eq)]
pub enum CommandStatus {
    #[serde(rename(serialize = "success"))]
    Success,

    #[serde(rename(serialize = "info"))]
    Info,

    #[serde(rename(serialize = "error"))]
    Error,
}
