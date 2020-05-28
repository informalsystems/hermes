use tendermint::abci;
use tendermint::rpc::endpoint::abci_query::AbciQuery;

use crate::error;
use crate::Height;

/// The type of IBC response sent back for a given IBC `Query`.
pub trait IbcResponse<Query>: Sized {
    /// The type of the raw response returned by the interface used to query the chain
    ///
    /// TODO: Uncomment once we abstract over the IBC client
    // type RawType;

    /// Build a response of this type from the initial `query` and the IBC `response`.
    ///
    /// TODO: Replace `AbciQuery` with `Self::RawType`
    fn from_abci_response(query: Query, response: AbciQuery) -> Result<Self, error::Error>;
}

/// Defines an IBC query
pub trait IbcQuery: Sized {
    type Response: IbcResponse<Self>;

    fn path(&self) -> abci::Path;
    fn height(&self) -> Height;
    fn prove(&self) -> bool;
    fn data(&self) -> Vec<u8>;

    /// Build a `Response` from a raw `AbciQuery` response
    ///
    /// TODO: Replace `AbciQuery` with `<Self::Response as IbcResponse<Self>>::RawType`
    fn build_response(self, response: AbciQuery) -> Result<Self::Response, error::Error> {
        Self::Response::from_abci_response(self, response)
    }
}
