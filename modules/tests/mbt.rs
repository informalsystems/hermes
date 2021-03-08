mod runner;

#[tokio::test]
async fn mbt() {
    // we should be able to just return the `Result` once the following
    // issue is fixed: https://github.com/rust-lang/rust/issues/43301
    if let Err(e) = all_tests().await {
        panic!("{}", e);
    }
}

async fn all_tests() -> Result<(), Box<dyn std::error::Error>> {
    // init tracing subscriber
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();

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
        println!("> running {}", test);

        // modelator options
        let options = modelator::Options::new("tests/support/model_based/IBCTests.tla")
            .tlc()
            .test(test)
            .workers(modelator::Workers::Auto);

        // run the test
        let runner = runner::IBCTestRunner::new();
        modelator::run(options, runner).await?;
    }

    Ok(())
}
