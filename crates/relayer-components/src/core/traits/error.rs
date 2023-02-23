use core::fmt::Debug;

use crate::core::traits::sync::Async;

/**
   This is used for contexts to declare that they have a _unique_ `Self::Error` type.

   Although it is possible for each context to declare their own associated
   `Error` type, doing so may result in having multiple ambiguous `Self::Error` types,
   if there are multiple associated types with the same name in different traits.

   As a result, it is better for context traits to include `HasError` as their
   parent traits, so that multiple traits can all refer to the same abstract
   `Self::Error` type.
*/
pub trait HasErrorType: Async {
    /**
       The `Error` associated type is also required to implement [`Debug`].

       This is to allow `Self::Error` to be used in calls like `.unwrap()`,
       as well as for simpler error logging.
    */
    type Error: Async + Debug;
}

/**
   Used for injecting external error types into [`Self::Error`](HasErrorType::Error).

   As an example, if `Context: InjectError<ParseIntError>`, then we would be
   able to call `Context::inject_error(err)` for an error value
   [`err: ParseIntError`](core::num::ParseIntError) and get back
   a [`Context::Error`](HasErrorType::Error) value.
*/
pub trait InjectError<E>: HasErrorType {
    fn inject_error(err: E) -> Self::Error;
}
