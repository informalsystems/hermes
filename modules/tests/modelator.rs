use eyre::{eyre, Context, Result};
use serde::de::DeserializeOwned;
use std::fmt::Debug;
use std::fs::File;
use std::io::BufReader;
use std::path::Path;

pub trait TestExecutor<S> {
    fn initial_step(&mut self, step: S) -> bool;
    fn next_step(&mut self, step: S) -> bool;
}

pub fn test_driver<Executor, Step, P>(mut executor: Executor, path: P) -> Result<()>
where
    Executor: TestExecutor<Step> + Debug,
    Step: DeserializeOwned + Debug + Clone,
    P: AsRef<Path>,
{
    // open test file
    let file = File::open(path.as_ref())
        .wrap_err_with(|| format!("test {:?} not found.", path.as_ref()))?;
    let reader = BufReader::new(file);

    // parse test file
    let steps: Vec<Step> = serde_json::de::from_reader(reader)
        .wrap_err_with(|| format!("test {:?} could not be deserialized", path.as_ref()))?;
    let step_count = steps.len();

    for (i, step) in steps.into_iter().enumerate() {
        // check the step
        let ok = if i == 0 {
            executor.initial_step(step.clone())
        } else {
            executor.next_step(step.clone())
        };

        if !ok {
            return Err(eyre!(
                "test {:?} failed on step {}/{}:\n{:#?}\n\nexecutor:\n{:#?}",
                path.as_ref(),
                i + 1,
                step_count,
                step,
                executor
            ));
        }
    }
    Ok(())
}
