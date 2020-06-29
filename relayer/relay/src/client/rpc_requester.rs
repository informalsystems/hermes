use async_trait::async_trait;

use tendermint::block::signed_header::SignedHeader as TMCommit;
use tendermint::block::Header as TMHeader;
use tendermint::lite::{error, Height, SignedHeader};
use tendermint::validator;
use tendermint::validator::Set;
use tendermint::{block, lite};
use tendermint_rpc as rpc;

/// RpcRequester wraps the Tendermint rpc::Client to provide
/// a slightly higher-level API to fetch signed headers
/// and validator sets from the chain.
pub struct RpcRequester {
    client: rpc::Client,
}

impl RpcRequester {
    pub fn new(client: rpc::Client) -> Self {
        Self { client }
    }
}

type TMSignedHeader = SignedHeader<TMCommit, TMHeader>;

#[async_trait]
impl lite::types::Requester<TMCommit, TMHeader> for RpcRequester {
    /// Request the signed header at height h.
    /// If h==0, request the latest signed header.
    /// TODO: use an enum instead of h==0.
    async fn signed_header(&self, h: Height) -> Result<TMSignedHeader, error::Error> {
        let height: block::Height = h.into();
        let r = match height.value() {
            0 => self.client.latest_commit().await,
            _ => self.client.commit(height).await,
        };
        match r {
            Ok(response) => Ok(response.signed_header.into()),
            Err(error) => Err(error::Kind::RequestFailed.context(error).into()),
        }
    }

    /// Request the validator set at height h.
    async fn validator_set(&self, h: Height) -> Result<Set, error::Error> {
        let r = self.client.validators(h).await;
        match r {
            Ok(response) => Ok(validator::Set::new(response.validators)),
            Err(error) => Err(error::Kind::RequestFailed.context(error).into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tendermint::lite::types::Header as LiteHeader;
    use tendermint::lite::types::Requester as LiteRequester;
    use tendermint::lite::types::ValidatorSet as LiteValSet;

    // TODO: integration test
    #[ignore]
    #[tokio::test]
    async fn test_val_set() {
        let client = rpc::Client::new("localhost:26657".parse().unwrap());
        let req = RpcRequester::new(client);

        let r1 = req.validator_set(5).await.unwrap();
        let r2 = req.signed_header(5).await.unwrap();

        assert_eq!(r1.hash(), r2.header().validators_hash());
    }
}
