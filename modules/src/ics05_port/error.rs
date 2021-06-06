use displaydoc::Display;
use flex_error::*;

pub type Error = anyhow::Error;

define_error! {
    UnknownPort
    | _ | { format_args!("pot unknown") },
}
