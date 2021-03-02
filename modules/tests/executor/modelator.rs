use serde::de::DeserializeOwned;
use std::fmt::Debug;
use std::fs::File;
use std::io::BufReader;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ModelatorError<Executor: Debug, Step: Debug> {
    #[error("test '{path}' not found: {error}")]
    TestNotFound { path: String, error: String },
    #[error("test '{path}' could not be deserialized: {error}")]
    InvalidTest { path: String, error: String },
    #[error("test '{path}' failed on step {step_index}/{step_count}:\nsteps: {steps:#?}\nexecutor: {executor:#?}")]
    FailedTest {
        path: String,
        step_index: usize,
        step_count: usize,
        steps: Vec<Step>,
        executor: Executor,
    },
}
pub trait TestExecutor<S> {
    fn initial_step(&mut self, step: S) -> bool;
    fn next_step(&mut self, step: S) -> bool;
}

pub fn test<Executor, State>(
    path: &str,
    mut executor: Executor,
) -> Result<(), ModelatorError<Executor, State>>
where
    Executor: TestExecutor<State> + Debug,
    State: DeserializeOwned + Debug + Clone,
{
    // open test file
    let file = File::open(path).map_err(|error| ModelatorError::TestNotFound {
        path: path.to_string(),
        error: error.to_string(),
    })?;
    let reader = BufReader::new(file);

    // parse test file
    let steps: Vec<State> =
        serde_json::de::from_reader(reader).map_err(|error| ModelatorError::InvalidTest {
            path: path.to_string(),
            error: error.to_string(),
        })?;
    let step_count = steps.len();

    for (i, step) in steps.iter().enumerate() {
        // check the step
        let ok = if i == 0 {
            executor.initial_step(step.clone())
        } else {
            executor.next_step(step.clone())
        };

        if !ok {
            return Err(ModelatorError::FailedTest {
                path: path.to_string(),
                step_index: i + 1,
                step_count,
                steps,
                executor,
            });
        }
    }
    Ok(())
}
