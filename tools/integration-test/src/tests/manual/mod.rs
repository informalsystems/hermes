/*!
    Tests that require manual human verification.

    Currently there are tests that require manual human observation of the
    relayer's behavior through the log messages to decide whether the test
    is working as expected. The test cases behind the [`manual`](self) module
    are only enabled when the `"manual"` feature flag is enabled manually.

    Any tests that require manual verification should be placed here.
    It is also fine to use [`suspend`](ibc_test_framework::util::suspend::suspend)
    inside the manual test, as the CI is not going to run the test.
*/

pub mod simulation;
