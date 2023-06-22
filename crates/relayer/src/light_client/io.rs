use tendermint::{account, block::Height};
use tendermint_light_client::{
    components::io::{AtHeight, Io, IoError, ProdIo},
    types::LightBlock,
};

#[derive(Clone, Debug)]
pub enum AnyIo {
    Prod(ProdIo),
    RestartAware(RestartAwareIo),
}

impl AnyIo {
    pub fn rpc_client(&self) -> &tendermint_rpc::HttpClient {
        match self {
            AnyIo::Prod(io) => io.rpc_client(),
            AnyIo::RestartAware(io) => io.rpc_client(),
        }
    }

    pub fn fetch_validator_set(
        &self,
        height: AtHeight,
        proposer_address: Option<account::Id>,
    ) -> Result<tendermint::validator::Set, IoError> {
        match self {
            AnyIo::Prod(io) => io.fetch_validator_set(height, proposer_address),
            AnyIo::RestartAware(io) => io.fetch_validator_set(height, proposer_address),
        }
    }
}

impl Io for AnyIo {
    fn fetch_light_block(&self, height: AtHeight) -> Result<LightBlock, IoError> {
        match self {
            AnyIo::Prod(io) => io.fetch_light_block(height),
            AnyIo::RestartAware(io) => io.fetch_light_block(height),
        }
    }
}

#[derive(Clone, Debug)]
pub struct RestartAwareIo {
    restart_height: Height,
    live_io: ProdIo,
    archive_io: ProdIo,
}

impl RestartAwareIo {
    pub fn new(restart_height: Height, live_io: ProdIo, archive_io: ProdIo) -> Self {
        Self {
            restart_height,
            live_io,
            archive_io,
        }
    }

    pub fn rpc_client(&self) -> &tendermint_rpc::HttpClient {
        self.live_io.rpc_client()
    }

    pub fn fetch_validator_set(
        &self,
        height: AtHeight,
        proposer_address: Option<account::Id>,
    ) -> Result<tendermint::validator::Set, IoError> {
        let io = match height {
            AtHeight::At(height) if height <= self.restart_height => &self.archive_io,
            _ => &self.live_io,
        };

        io.fetch_validator_set(height, proposer_address)
    }
}

impl Io for RestartAwareIo {
    fn fetch_light_block(&self, height: AtHeight) -> Result<LightBlock, IoError> {
        let io = match height {
            AtHeight::At(height) if height <= self.restart_height => &self.archive_io,
            _ => &self.live_io,
        };

        io.fetch_light_block(height)
    }
}
