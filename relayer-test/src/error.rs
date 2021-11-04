//! Error type used for the tests.

/**
   Right now we simply use [`eyre::Report`] as the untyped error type
   for the tests. This is because we do not need to handle any error
   during test and they are simply propagated and become a test failure.
*/
pub use eyre::Report as Error;
