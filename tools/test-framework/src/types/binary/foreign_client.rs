use crate::relayer::foreign_client::TaggedForeignClientExt;
use crate::types::id::TaggedClientIdRef;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::ForeignClient;

#[derive(Clone)]
pub struct ForeignClientPair<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub client_a_to_b: ForeignClient<ChainB, ChainA>,
    pub client_b_to_a: ForeignClient<ChainA, ChainB>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> ForeignClientPair<ChainA, ChainB> {
    pub fn new(
        client_a_to_b: ForeignClient<ChainB, ChainA>,
        client_b_to_a: ForeignClient<ChainA, ChainB>,
    ) -> Self {
        Self {
            client_a_to_b,
            client_b_to_a,
        }
    }

    pub fn client_id_a(&self) -> TaggedClientIdRef<ChainA, ChainB> {
        self.client_b_to_a.tagged_client_id()
    }

    pub fn client_id_b(&self) -> TaggedClientIdRef<ChainB, ChainA> {
        self.client_a_to_b.tagged_client_id()
    }

    pub fn handle_a(&self) -> ChainA {
        self.client_b_to_a.dst_chain()
    }

    pub fn handle_b(&self) -> ChainB {
        self.client_a_to_b.dst_chain()
    }

    /**
       Switch the position between chain A and chain B.

       The original chain B become the new chain A, and the original chain A
       become the new chain B.
    */
    pub fn flip(self) -> ForeignClientPair<ChainB, ChainA> {
        ForeignClientPair {
            client_a_to_b: self.client_b_to_a,
            client_b_to_a: self.client_a_to_b,
        }
    }

    pub fn map_chain<ChainC: ChainHandle, ChainD: ChainHandle>(
        self,
        map_a: &impl Fn(ChainA) -> ChainC,
        map_b: &impl Fn(ChainB) -> ChainD,
    ) -> ForeignClientPair<ChainC, ChainD> {
        ForeignClientPair {
            client_a_to_b: self.client_a_to_b.map_chain(map_b, map_a),
            client_b_to_a: self.client_b_to_a.map_chain(map_a, map_b),
        }
    }
}
