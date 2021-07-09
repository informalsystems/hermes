use std::{collections::BTreeMap, fmt};

use ibc::ics24_host::identifier::ChainId;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use tracing::info;

use crate::object::{Object, ObjectType};

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct SupervisorState {
    pub chains: Vec<ChainId>,
    pub workers: BTreeMap<ObjectType, Vec<Object>>,
}

impl SupervisorState {
    pub fn new(chains: Vec<ChainId>, workers: BTreeMap<ObjectType, Vec<Object>>) -> Self {
        Self { chains, workers }
    }

    pub fn print_info(&self) {
        self.to_string()
            .split('\n')
            .for_each(|line| info!("{}", line));
    }
}

impl fmt::Display for SupervisorState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f)?;
        writeln!(f, "* Chains: {}", self.chains.iter().join(", "))?;
        for (tpe, objects) in &self.workers {
            writeln!(f, "* {:?} workers:", tpe)?;
            for object in objects {
                writeln!(f, "  - {}", object.short_name())?;
            }
        }

        Ok(())
    }
}
