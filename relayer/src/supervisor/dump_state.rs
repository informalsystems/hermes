use std::{collections::BTreeMap, fmt};

use ibc::ics24_host::identifier::ChainId;
use serde::{Deserialize, Serialize};
use tracing::info;

use crate::object::{Object, ObjectType};

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct SupervisorState {
    pub chains: BTreeMap<ChainId, BTreeMap<ObjectType, Vec<Object>>>,
}

impl SupervisorState {
    pub fn print_info(&self) {
        self.to_string()
            .split('\n')
            .for_each(|line| info!("{}", line));
    }
}

impl fmt::Display for SupervisorState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f)?;
        for (chain, objects_map) in &self.chains {
            writeln!(f, "# {}:", chain)?;
            for (tpe, objects) in objects_map {
                writeln!(f, "* {:?} workers:", tpe)?;
                for object in objects {
                    writeln!(f, "  - {}", object.short_name())?;
                }
            }
        }

        Ok(())
    }
}
