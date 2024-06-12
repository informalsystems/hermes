/*!
   The Topology defines how chains are interconnected when more than two are used in tests.
   This setup is managed by the [`crate::bootstrap::nary::chain::boostrap_chains_with_any_nodes`]
   function.

   Connections are established by examining the existing clients, and channels are created based
   on these connections. Therefore, to define the topology of the chains, it is sufficient to
   create the appropriate set of clients.

   Example: Linear Topology

   For a linear topology between chains A, B, and C, the clients are created as follows:
   * Chain A: a client referencing chain B
   * Chain B: a client referencing chain B and a client referencing chain C
   * Chain C: a client referencing chain B

   This setup ensures that:

   * Chain A is connected to Chain B.
   * Chain B is connected to both Chain A and Chain C.
   * Chain C is connected to Chain B.

   Example: Fully Connected Topology

   In a fully connected topology, every chain has clients referencing all other chains.
   For chains A, B, and C, the clients are created as follows:

   * Chain A: Clients referencing chains B and C
   * Chain B: Clients referencing chains A and C
   * Chain C: Clients referencing chains A and B

   This setup ensures that every chain is directly connected to every other chain, forming
   a complete graph.

   By defining the appropriate set of clients, you can establish the desired topology for
   your tests, whether it be linear, fully connected, or any other configuration.
*/

use eyre::eyre;
use std::collections::HashMap;
use std::str::FromStr;

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use crate::bootstrap::binary::chain::bootstrap_foreign_client;
use crate::error::Error;

pub enum TopologyTypes {
    Linear,
    Full,
}

impl FromStr for TopologyTypes {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "linear" => Ok(Self::Linear),
            "full" => Ok(Self::Full),
            _ => Err(Error::generic(eyre!("The topology `{s}` does not exist"))),
        }
    }
}

pub trait Topology<Handle: ChainHandle> {
    fn get_topology(
        &self,
        chain_handles: &Vec<Handle>,
    ) -> Result<HashMap<usize, HashMap<usize, ForeignClient<Handle, Handle>>>, Error>;
}

pub struct FullyConnectedTopology;

impl<Handle: ChainHandle> Topology<Handle> for FullyConnectedTopology {
    fn get_topology(
        &self,
        chain_handles: &Vec<Handle>,
    ) -> Result<HashMap<usize, HashMap<usize, ForeignClient<Handle, Handle>>>, Error> {
        let mut foreign_clients: HashMap<usize, HashMap<usize, ForeignClient<_, _>>> =
            HashMap::new();

        for (i, handle_a) in chain_handles.iter().enumerate() {
            let mut foreign_clients_b = HashMap::new();

            for (j, handle_b) in chain_handles.iter().enumerate() {
                let foreign_client =
                    bootstrap_foreign_client(handle_a, handle_b, Default::default())?;

                foreign_clients_b.insert(j, foreign_client);
            }

            foreign_clients.insert(i, foreign_clients_b);
        }
        Ok(foreign_clients)
    }
}

pub struct LinearTopology;

impl<Handle: ChainHandle> Topology<Handle> for LinearTopology {
    fn get_topology(
        &self,
        chain_handles: &Vec<Handle>,
    ) -> Result<HashMap<usize, HashMap<usize, ForeignClient<Handle, Handle>>>, Error> {
        let mut foreign_clients: HashMap<usize, HashMap<usize, ForeignClient<_, _>>> =
            HashMap::new();

        let last_index = chain_handles.len() - 1;
        for (i, _) in chain_handles.iter().enumerate() {
            let mut clients = HashMap::new();
            if i < last_index {
                let client = bootstrap_foreign_client(
                    &chain_handles[i],
                    &chain_handles[i + 1],
                    Default::default(),
                )?;
                clients.insert(i + 1, client);
            }
            if i > 0 {
                let client = bootstrap_foreign_client(
                    &chain_handles[i],
                    &chain_handles[i - 1],
                    Default::default(),
                )?;
                clients.insert(i - 1, client);
            }

            foreign_clients.insert(i, clients);
        }
        Ok(foreign_clients)
    }
}

pub fn get_topology<Handle: ChainHandle>(value: &str) -> Box<dyn Topology<Handle>> {
    if let Ok(topology_type) = value.parse() {
        match topology_type {
            TopologyTypes::Full => Box::new(FullyConnectedTopology),
            TopologyTypes::Linear => Box::new(LinearTopology),
        }
    } else {
        tracing::warn!("Failed to parse topology type `{value}`. Will fallback to Linear topology");
        Box::new(LinearTopology)
    }
}
