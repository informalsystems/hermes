extern crate alloc;

mod runner;

use modelator::{
    model::checker::{ModelChecker, ModelCheckerRuntime},
    Error,
};
use runner::IbcTestRunner;

#[test]
fn mbt() {
    // we should be able to just return the `Result` once the following
    // issue is fixed: https://github.com/rust-lang/rust/issues/43301
    if let Err(e) = run_tests() {
        panic!("{}", e);
    }
}

fn run_tests() -> Result<(), Error> {
    // run the test
    let tla_tests_file = "tests/support/model_based/IBCTests.tla";
    let tla_config_file = "tests/support/model_based/IBCTests.cfg";
    let runtime = modelator::ModelatorRuntime::default()
        .model_checker_runtime(ModelCheckerRuntime::default().model_checker(ModelChecker::Tlc));

    let mut runner = IbcTestRunner::new();
    runtime.run_tla_steps(tla_tests_file, tla_config_file, &mut runner)?;
    Ok(())
}
