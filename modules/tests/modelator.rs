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
        .wrap_err_with(|| format!("test file {:?} not found.", path.as_ref()))?;
    let reader = BufReader::new(file);

    // parse test file
    let steps: Vec<Step> = serde_json::de::from_reader(reader)
        .wrap_err_with(|| format!("test file {:?} could not be deserialized", path.as_ref()))?;

    let mut steps = steps.into_iter();

    // check the initial step
    if let Some(step) = steps.next() {
        if !executor.initial_step(step.clone()) {
            return Err(eyre!("check failed on initial step:\n{:#?}", step));
        }
    } else {
        println!("WARNING: test file {:?} had 0 steps", path.as_ref());
        return Ok(());
    }

    // check the remaining steps
    for step in steps {
        if !executor.next_step(step.clone()) {
            return Err(eyre!(
                "check failed on step:\n{:#?}\n\nexecutor:\n{:#?}",
                step,
                executor
            ));
        }
    }
    Ok(())
}
