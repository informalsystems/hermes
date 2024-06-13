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
   * Each chain will also have a self referencing client

   This setup ensures that every chain is directly connected to every other chain, forming
   a complete graph.

   Example: Cyclic Topology

   The cyclic topology is similar to the linear topology with the addition of the first and
   last chain being connected as well.
   For chains A, B, C and D, the clients are created as follows:

   * Chain A: Clients referencing chains B and D
   * Chain B: Clients referencing chains A and C
   * Chain C: Clients referencing chains B and D
   * Chain D: Clients referencing chains A and C

   By defining the appropriate set of clients, you can establish the desired topology for
   your tests, whether it be linear, fully connected, or any other configuration.
*/

use eyre::eyre;
use std::str::FromStr;

use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

use crate::bootstrap::binary::chain::bootstrap_foreign_client;
use crate::error::Error;
use crate::util::two_dim_hash_map::TwoDimMap;

pub enum TopologyType {
    Linear,
    Full,
    Cyclic,
}

impl FromStr for TopologyType {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "linear" => Ok(Self::Linear),
            "full" => Ok(Self::Full),
            "cyclic" => Ok(Self::Cyclic),
            _ => Err(Error::generic(eyre!("The topology `{s}` does not exist"))),
        }
    }
}

pub trait Topology<Handle: ChainHandle> {
    fn create_topology(
        &self,
        chain_handles: &Vec<Handle>,
    ) -> Result<TwoDimMap<ForeignClient<Handle, Handle>>, Error>;
}

pub struct FullyConnectedTopology;

impl<Handle: ChainHandle> Topology<Handle> for FullyConnectedTopology {
    fn create_topology(
        &self,
        chain_handles: &Vec<Handle>,
    ) -> Result<TwoDimMap<ForeignClient<Handle, Handle>>, Error> {
        let mut foreign_clients: TwoDimMap<ForeignClient<_, _>> = TwoDimMap::new();

        for (i, handle_a) in chain_handles.iter().enumerate() {
            for (j, handle_b) in chain_handles.iter().enumerate() {
                let foreign_client =
                    bootstrap_foreign_client(handle_a, handle_b, Default::default())?;

                foreign_clients.insert((i, j), foreign_client);
            }
        }
        Ok(foreign_clients)
    }
}

pub struct LinearTopology;

impl<Handle: ChainHandle> Topology<Handle> for LinearTopology {
    fn create_topology(
        &self,
        chain_handles: &Vec<Handle>,
    ) -> Result<TwoDimMap<ForeignClient<Handle, Handle>>, Error> {
        let mut foreign_clients: TwoDimMap<ForeignClient<_, _>> = TwoDimMap::new();

        let last_index = chain_handles.len() - 1;
        for (i, _) in chain_handles.iter().enumerate() {
            if i < last_index {
                let client = bootstrap_foreign_client(
                    &chain_handles[i],
                    &chain_handles[i + 1],
                    Default::default(),
                )?;
                foreign_clients.insert((i, i + 1), client);
            }
            if i > 0 {
                let client = bootstrap_foreign_client(
                    &chain_handles[i],
                    &chain_handles[i - 1],
                    Default::default(),
                )?;
                foreign_clients.insert((i, i - 1), client);
            }
        }
        Ok(foreign_clients)
    }
}

pub struct CyclicTopology;

impl<Handle: ChainHandle> Topology<Handle> for CyclicTopology {
    fn create_topology(
        &self,
        chain_handles: &Vec<Handle>,
    ) -> Result<TwoDimMap<ForeignClient<Handle, Handle>>, Error> {
        let mut foreign_clients: TwoDimMap<ForeignClient<_, _>> = TwoDimMap::new();

        let last_index = chain_handles.len() - 1;
        for (i, _) in chain_handles.iter().enumerate() {
            // Create client from first chain to last
            if i == 0 {
                let client = bootstrap_foreign_client(
                    &chain_handles[0],
                    &chain_handles[last_index],
                    Default::default(),
                )?;
                foreign_clients.insert((i, last_index), client);
            }
            // Create client from last chain to first
            if i == last_index {
                let client = bootstrap_foreign_client(
                    &chain_handles[last_index],
                    &chain_handles[0],
                    Default::default(),
                )?;
                foreign_clients.insert((i, 0), client);
            }
            if i < last_index {
                let client = bootstrap_foreign_client(
                    &chain_handles[i],
                    &chain_handles[i + 1],
                    Default::default(),
                )?;
                foreign_clients.insert((i, i + 1), client);
            }
            if i > 0 {
                let client = bootstrap_foreign_client(
                    &chain_handles[i],
                    &chain_handles[i - 1],
                    Default::default(),
                )?;
                foreign_clients.insert((i, i - 1), client);
            }
        }
        Ok(foreign_clients)
    }
}

pub fn bootstrap_topology<Handle: ChainHandle>(
    topology: TopologyType,
) -> Box<dyn Topology<Handle>> {
    match topology {
        TopologyType::Full => Box::new(FullyConnectedTopology),
        TopologyType::Linear => Box::new(LinearTopology),
        TopologyType::Cyclic => Box::new(CyclicTopology),
    }
}
