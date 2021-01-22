use abscissa_core::config;

use ibc::ics24_host::identifier::ChainId;
use relayer::chain::handle::ChainHandle;
use relayer::chain::runtime::ChainRuntime;
use relayer::chain::CosmosSDKChain;

use crate::application::CliApp;
use crate::error::{Error, Kind};

/// Pair of chain handlers that are used by most CLIs.
pub struct ChainHandlePair {
    /// Source chain handle
    pub src: Box<dyn ChainHandle>,
    /// Destination chain handle
    pub dst: Box<dyn ChainHandle>,
}

/// Create the source and destination chain handlers from the configuration and chain identifiers
pub fn chain_handlers_from_chain_id(
    config: config::Reader<CliApp>,
    src_chain_id: &ChainId,
    dst_chain_id: &ChainId,
) -> Result<ChainHandlePair, Error> {
    let src_config = config
        .find_chain(src_chain_id)
        .ok_or_else(|| "missing source chain in configuration file".to_string());

    let dst_config = config
        .find_chain(dst_chain_id)
        .ok_or_else(|| "missing destination chain configuration file".to_string());

    let (src_chain_config, dst_chain_config) = match (src_config, dst_config) {
        (Ok(s), Ok(d)) => (s, d),
        (Err(e), _) | (_, Err(e)) => {
            return Err(Kind::Config.context(e).into());
        }
    };

    let src_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(src_chain_config.clone())
        .map_err(|e| Kind::Runtime.context(e));
    let src = match src_chain_res {
        Ok((handle, _)) => handle,
        Err(e) => {
            return Err(e.into());
        }
    };

    let dst_chain_res = ChainRuntime::<CosmosSDKChain>::spawn(dst_chain_config.clone())
        .map_err(|e| Kind::Runtime.context(e));
    let dst = match dst_chain_res {
        Ok((handle, _)) => handle,
        Err(e) => {
            return Err(e.into());
        }
    };

    Ok(ChainHandlePair { src, dst })
}
