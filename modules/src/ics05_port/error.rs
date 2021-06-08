use flex_error::*;

pub type Error = anyhow::Error;

define_error! { PortError;
    UnknownPort
    [DisplayError<Error>]
    | _ | { format_args!("pot unknown") },
}
