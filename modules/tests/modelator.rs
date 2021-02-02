use eyre::{eyre, Context, Result};
use serde::de::DeserializeOwned;
use std::fmt::Debug;
use std::fs::File;
use std::path::Path;

pub trait TestExecutor<S> {
    fn check_initial_state(&mut self, state: S) -> bool;

    fn check_next_state(&mut self, state: S) -> bool;
}

pub fn test_driver<E, S, P>(mut executor: E, path: P) -> Result<()>
where
    E: TestExecutor<S> + Debug,
    S: DeserializeOwned + Debug + Clone,
    P: AsRef<Path>,
{
    let reader = File::open(path.as_ref())
        .wrap_err_with(|| format!("test file {:?} not found.", path.as_ref()))?;
    let states: Vec<S> = serde_json::de::from_reader(reader)
        .wrap_err_with(|| format!("test file {:?} could not be deserialized", path.as_ref()))?;

    let mut states = states.into_iter();

    if let Some(state) = states.next() {
        if !executor.check_initial_state(state.clone()) {
            return Err(eyre!("check failed on initial state:\n{:#?}", state));
        }
    } else {
        println!("WARNING: test file {:?} had 0 states", path.as_ref());
        return Ok(());
    }

    for state in states {
        if !executor.check_next_state(state.clone()) {
            return Err(eyre!(
                "check failed on state:\n{:#?}\n\nexecutor:\n{:#?}",
                state,
                executor
            ));
        }
    }
    Ok(())
}
