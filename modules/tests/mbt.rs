mod executor;

const TESTS_DIR: &str = "tests/support/model_based/tests";

#[test]
fn mbt() {
    let tests = vec![
        "ICS02CreateOKTest",
        "ICS02UpdateOKTest",
        "ICS02ClientNotFoundTest",
        "ICS02HeaderVerificationFailureTest",
        "ICS03ConnectionOpenInitOKTest",
        "ICS03MissingClientTest",
        "ICS03ConnectionOpenTryOKTest",
        "ICS03InvalidConsensusHeightTest",
        "ICS03ConnectionNotFoundTest",
        "ICS03ConnectionMismatchTest",
        "ICS03MissingClientConsensusStateTest",
        // TODO: the following test should fail but doesn't because proofs are
        // not yet verified
        // "ICS03InvalidProofTest",
        "ICS03ConnectionOpenAckOKTest",
        "ICS03UninitializedConnectionTest",
        "ICS03ConnectionOpenConfirmOKTest",
    ];

    for test in tests {
        let test = format!("{}/{}.json", TESTS_DIR, test);
        println!("> running {}", test);
        let executor = executor::IBCTestExecutor::new();
        // we should be able to just return the `Result` once the following
        // issue is fixed: https://github.com/rust-lang/rust/issues/43301
        if let Err(e) = executor::modelator::test(&test, executor) {
            panic!("{}", e);
        }
    }
}
