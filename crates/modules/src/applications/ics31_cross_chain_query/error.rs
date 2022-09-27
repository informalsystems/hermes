use flex_error::define_error;

define_error! {
    #[derive(Debug, PartialEq, Eq)]
    Error {
        Parse
            | _ | { "parse error" }
    }
}
