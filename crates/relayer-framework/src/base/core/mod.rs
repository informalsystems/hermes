/*!
   Core constructs common for all contexts.

   This module contains the common constructs that are usable across all
   contexts. This includes:

   - The [`Async`](traits::sync::Async) trait is used  to constraint
       abstract types so that they are safe to use inside async functions.

   - The [`HasErrorType`](traits::error::HasErrorType) trait is used for contexts
       to declare a single abstract `Error` type.
*/

pub mod traits;
