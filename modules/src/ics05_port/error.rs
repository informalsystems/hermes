#[cfg(not(feature = "std"))]
impl crate::primitives::StdError for Error {}

use flex_error::define_error;

define_error! {
    Error {
        UnknownPort
            | _ | { format_args!("port unknown") }
    }
}
