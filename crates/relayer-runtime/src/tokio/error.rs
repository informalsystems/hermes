use flex_error::define_error;

define_error! {
    #[derive(Clone, Debug)]
    Error {
        ChannelClosed
            | _ | { "unexpected closure of internal rust channels" },

        PoisonedLock
            | _ | { "poisoned mutex lock" },
    }
}
