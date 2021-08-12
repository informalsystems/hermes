use flex_error::define_error;

define_error! {
    Error {
        UnknownPort
            | _ | { format_args!("port unknown") }
    }
}
