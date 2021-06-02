use flex_error::*;

pub type Error = anyhow::Error;

define_error! {
    #[derive(Debug)]
    PortError {
        UnknownPort
        [DisplayError<Error>]
        | _ | { format_args!("pot unknown") },
    }
}
