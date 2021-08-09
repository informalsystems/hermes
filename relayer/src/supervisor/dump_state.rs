use std::{collections::BTreeMap, fmt};

use ibc::ics24_host::identifier::ChainId;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use tracing::info;

use crate::{
    object::{Object, ObjectType},
    worker::WorkerId,
};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WorkerDesc<Chain, Counterparty> {
    pub id: WorkerId,
    pub object: Object<Chain, Counterparty>,
}

impl<Chain, Counterparty> WorkerDesc<Chain, Counterparty> {
    pub fn new(id: WorkerId, object: Object<Chain, Counterparty>) -> Self {
        Self { id, object }
    }
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct SupervisorState<Chain, Counterparty> {
    pub chains: Vec<ChainId>,
    pub workers: BTreeMap<ObjectType, Vec<WorkerDesc<Chain, Counterparty>>>,
}

impl<Chain, Counterparty> SupervisorState<Chain, Counterparty> {
    pub fn new<'a>(
        mut chains: Vec<ChainId>,
        workers: impl Iterator<Item = (WorkerId, &'a Object<Chain, Counterparty>)>,
    ) -> Self
    where
        Chain: 'a,
        Counterparty: 'a,
    {
        chains.sort();

        let workers = workers
            .map(|(id, o)| WorkerDesc::new(id, o.clone()))
            .into_group_map_by(|desc| desc.object.object_type())
            .into_iter()
            .update(|(_, os)| os.sort_by_key(|desc| desc.object.short_name()))
            .collect::<BTreeMap<_, _>>();

        Self { chains, workers }
    }

    pub fn print_info(&self) {
        self.to_string()
            .split('\n')
            .for_each(|line| info!("{}", line));
    }
}

impl<Chain, Counterparty> fmt::Display for SupervisorState<Chain, Counterparty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f)?;
        writeln!(f, "* Chains: {}", self.chains.iter().join(", "))?;
        for (tpe, objects) in &self.workers {
            writeln!(f, "* {:?} workers:", tpe)?;
            for desc in objects {
                writeln!(f, "  - {} (id: {})", desc.object.short_name(), desc.id)?;
            }
        }

        Ok(())
    }
}
