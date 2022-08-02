pub struct OfaErrorContext<Error> {
    pub error: Error,
}

impl<Error> OfaErrorContext<Error> {
    pub fn new(error: Error) -> Self {
        Self { error }
    }
}
