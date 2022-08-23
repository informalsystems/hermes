use flex_error::define_error;

define_error! {
    Error {
        ChannelClosed
            | _ | { "unexpected closure of internal rust channels" },
    }
}
