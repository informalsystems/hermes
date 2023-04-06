use tendermint::block::Height;
use tendermint_light_client::{
    components::io::{AtHeight, Io, IoError, ProdIo},
    types::LightBlock,
};

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
