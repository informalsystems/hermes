mod runner;

use modelator::{run, TestError};
use runner::{step::Step, IbcTestRunner};

#[test]
fn mbt() {
    // we should be able to just return the `Result` once the following
    // issue is fixed: https://github.com/rust-lang/rust/issues/43301
    if let Err(e) = run_tests() {
        panic!("{}", e);
    }
}

fn run_tests() -> Result<(), TestError<IbcTestRunner, Step>> {
    // run the test
    let tla_tests_file = "tests/support/model_based/IBCTests.tla";
    let tla_config_file = "tests/support/model_based/IBCTests.cfg";
    let runner = IbcTestRunner::new();
    run(tla_tests_file, tla_config_file, runner)?;

    Ok(())
}
