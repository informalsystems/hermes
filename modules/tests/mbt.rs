mod executor;

const TESTS_DIR: &str = "tests/support/model_based/tests";

#[test]
fn mbt() {
    let tests = vec!["ICS02UpdateOKTest", "ICS02HeaderVerificationFailureTest"];

    for test in tests {
        let test = format!("{}/{}.json", TESTS_DIR, test);
        let executor = executor::IBCTestExecutor::new();
        // we should be able to just return the `Result` once the following issue
        // is fixed: https://github.com/rust-lang/rust/issues/43301
        if let Err(e) = executor::modelator::test(&test, executor) {
            panic!("{:?}", e);
        }
    }
}
