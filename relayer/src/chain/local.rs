use crate::config::LocalChainConfig;
use crate::error::Error;
use ibc::handler::HandlerOutput;
use ibc::ics02_client::client_def::{AnyClientState, AnyHeader};
use ibc::ics18_relayer::context::ICS18Context;
use ibc::ics18_relayer::error::Error as ICS18Error;
use ibc::ics24_host::identifier::ClientId;
use ibc::ics26_routing::msgs::ICS26Envelope;
use ibc::Height;

#[allow(dead_code)]
pub struct LocalChain {
    config: LocalChainConfig,
    height: u64,
}

#[allow(dead_code)]
impl LocalChain {
    pub fn from_config(config: LocalChainConfig) -> Result<Self, Error> {
        Ok(Self { config, height: 1 })
    }

    // TODO -- add a generic interface to submit any type of IBC datagram.
    /// Submits an IBC message for creating an IBC client on the chain. It is assumed that this is
    /// a client for a mock chain.
    pub fn create_client(&self, _client_id: &str) {
        unimplemented!()
    }

    /// Advances the chain height, by appending a new light block to its history.
    pub fn advance(&mut self) {
        self.height += 1;
    }
}

impl ICS18Context for LocalChain {
    fn query_latest_height(&self) -> Height {
        Height::from(self.height)
    }

    fn query_client_full_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        unimplemented!()
    }

    fn query_latest_header(&self) -> Option<AnyHeader> {
        unimplemented!()
    }

    fn send(&mut self, msg: ICS26Envelope) -> Result<HandlerOutput<()>, ICS18Error> {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use crate::chain::local::LocalChain;
    use crate::config::LocalChainConfig;
    use ibc::ics18_relayer::context::ICS18Context;
    use ibc::ics18_relayer::utils::create_client_update_datagram;
    use ibc::ics24_host::identifier::ClientId;
    use ibc::Height;
    use std::str::FromStr;
    use tendermint::chain::Id as ChainId;

    #[test]
    fn create_local_chain() {
        let cfg = LocalChainConfig {
            id: ChainId::from_str("not-gaia").unwrap(),
            client_ids: vec![String::from("client_one"), String::from("client_two")],
        };

        let c = LocalChain::from_config(cfg);
        assert!(c.is_ok())
    }

    #[test]
    // Simple test for the advance chain function.
    fn chain_advance() {
        let update_count = 4; // Number of advance chain iterations.
        let cfg = LocalChainConfig {
            id: ChainId::from_str("chain-a").unwrap(),
            client_ids: vec![String::from("client_on_a_for_b")],
        };
        let chain_res = LocalChain::from_config(cfg);
        assert!(chain_res.is_ok());
        let mut chain = chain_res.unwrap();

        let mut current_height = u64::from(chain.query_latest_height());

        for _i in 0..update_count {
            chain.advance();
            let new_height = u64::from(chain.query_latest_height());
            assert_eq!(
                new_height,
                current_height + 1,
                "advance(): fails to increase the latest height"
            );

            current_height = new_height;
        }
    }

    #[test]
    /// Tests the relayer `create_client_update_datagram` of ICS18 against two generated
    /// Tendermint chains (see `testgen` crate).
    /// Note: This is a more realistic version of test `client_update_ping_pong` of ICS18.
    fn tm_chains_ping_pong() {
        let update_count = 4; // Number of ping-pong (client update) iterations.
        let client_on_a_for_b = ClientId::from_str("client_on_a_for_b").unwrap();
        let client_on_b_for_a = ClientId::from_str("client_on_b_for_a").unwrap();

        let cfg_a = LocalChainConfig {
            id: ChainId::from_str("chain-a").unwrap(),
            client_ids: vec![client_on_a_for_b.to_string()],
        };
        let cfg_b = LocalChainConfig {
            id: ChainId::from_str("chain-b").unwrap(),
            client_ids: vec![client_on_b_for_a.to_string()],
        };

        let chain_a = LocalChain::from_config(cfg_a).unwrap();
        let chain_b = LocalChain::from_config(cfg_b).unwrap();

        for _i in 0..update_count {
            let a_latest_header = chain_a.query_latest_header().unwrap();
            let client_msg_b_res =
                create_client_update_datagram(&chain_b, &client_on_b_for_a, a_latest_header);
            assert!(client_msg_b_res.is_ok())
        }
    }
}
