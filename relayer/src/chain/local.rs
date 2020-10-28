use crate::config::LocalChainConfig;
use crate::error::{Error, Kind};
use ibc::handler::HandlerOutput;
use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use ibc::ics02_client::client_type::ClientType;
use ibc::ics02_client::context::{ClientKeeper, ClientReader};
use ibc::ics02_client::error::Error as ICS02Error;
use ibc::ics02_client::msgs::{ClientMsg, MsgCreateAnyClient};
use ibc::ics03_connection::connection::ConnectionEnd;
use ibc::ics03_connection::context::{ConnectionKeeper, ConnectionReader};
use ibc::ics03_connection::error::Error as ICS03Error;
use ibc::ics18_relayer::context::ICS18Context;
use ibc::ics18_relayer::error::Error as ICS18Error;
use ibc::ics18_relayer::error::Kind as ICS18Kind;
use ibc::ics23_commitment::commitment::CommitmentPrefix;
use ibc::ics24_host::identifier::{ClientId, ConnectionId};
use ibc::ics26_routing::context::ICS26Context;
use ibc::ics26_routing::msgs::ICS26Envelope;
use ibc::Height;

use ibc::mock::context::MockContext;

use ibc::ics26_routing::handler::dispatch;
use std::str::FromStr;
use tendermint::account::Id as AccountId;
use tendermint_light_client::types::LightBlock;

/// A Tendermint chain locally running in-process with the relayer. Wraps over a `MockContext`,
/// which does most of the heavy lifting of implementing IBC dependencies.
pub struct LocalChain {
    config: LocalChainConfig,
    context: MockContext,
}

/// Internal interface, for writing relayer tests.
impl LocalChain {
    pub fn from_config(config: LocalChainConfig) -> Result<Self, Error> {
        Ok(Self {
            config,
            context: MockContext::default(),
        })
    }

    /// Submits an IBC message for creating an IBC client on the chain. It is assumed that this is
    /// a client for a mock chain.
    pub fn create_client(&mut self, client_id: &ClientId) -> Result<(), Error> {
        let client_message = ClientMsg::CreateClient(
            MsgCreateAnyClient::new(
                client_id.clone(),
                todo!(),
                todo!(),
                AccountId::from_str("0CDA3F47EF3C4906693B170EF650EB968C5F4B2C").unwrap(),
            )
            .unwrap(),
        );

        self.send(ICS26Envelope::ICS2Msg(client_message))
            .map_err(|_| {
                Kind::CreateClient(client_id.clone(), "tx submission failed".into()).into()
            })
    }
}

/// The relayer-facing interface.
impl ICS18Context for LocalChain {
    fn query_latest_height(&self) -> Height {
        todo!()
    }

    fn query_client_full_state(&self, client_id: &ClientId) -> Option<AnyClientState> {
        unimplemented!()
    }

    fn query_latest_header(&self) -> Option<AnyHeader> {
        unimplemented!()
    }

    fn send(&mut self, msg: ICS26Envelope) -> Result<(), ICS18Error> {
        // Forward the datagram directly into ICS26 routing handler.
        // dispatch(self.context, msg).map_err(|e| ICS18Kind::TransactionFailed.context(e))?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::chain::local::LocalChain;
    use crate::config::LocalChainConfig;
    use ibc::ics18_relayer::context::ICS18Context;
    use ibc::ics18_relayer::utils::create_client_update_datagram;
    use ibc::ics24_host::identifier::ClientId;
    use ibc::ics26_routing::msgs::ICS26Envelope;
    use ibc::Height;
    use std::str::FromStr;
    use tendermint::chain::Id as ChainId;

    #[test]
    fn create_local_chain_and_client() {
        let _client_id = ClientId::from_str("clientonlocalchain").unwrap();
        let cfg = LocalChainConfig {
            id: ChainId::from_str("not-gaia").unwrap(),
            client_ids: vec![String::from("client_one"), String::from("client_two")],
        };

        let c = LocalChain::from_config(cfg);
        assert!(c.is_ok());

        let mut _chain = c.unwrap();
        // assert!(chain.create_client(&client_id).is_ok());
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
        // let mut chain = chain_res.unwrap();

        // let mut current_height = chain.query_latest_height();
        //
        // for _i in 0..update_count {
        //     chain.advance();
        //     let new_height = chain.query_latest_height();
        //     assert_eq!(
        //         new_height,
        //         current_height.increment(),
        //         "advance(): fails to increase the latest height"
        //     );
        //
        //     current_height = new_height;
        // }
    }

    #[test]
    /// Tests the relayer `create_client_update_datagram` of ICS18 against two generated
    /// Tendermint chains (see `testgen` crate).
    /// Note: This is a more realistic version of test `client_update_ping_pong` of ICS18.
    fn tm_client_update_ping_pong() {
        let _update_count = 4; // Number of ping-pong (client update) iterations.
        let client_on_a_for_b = ClientId::from_str("client_on_a_for_b").unwrap();
        let client_on_b_for_a = ClientId::from_str("client_on_b_for_a").unwrap();

        let _cfg_a = LocalChainConfig {
            id: ChainId::from_str("chain-a").unwrap(),
            client_ids: vec![client_on_a_for_b.to_string()],
        };
        let _cfg_b = LocalChainConfig {
            id: ChainId::from_str("chain-b").unwrap(),
            client_ids: vec![client_on_b_for_a.to_string()],
        };

        // let chain_a = LocalChain::from_config(cfg_a).unwrap();
        // let mut chain_b = LocalChain::from_config(cfg_b).unwrap();

        // for _i in 0..update_count {
        //     // Figure out if we need to create a ClientUpdate datagram for client of A on chain B.
        //     let a_latest_header = chain_a.query_latest_header().unwrap();
        //     let client_msg_b_res =
        //         create_client_update_datagram(&chain_b, &client_on_b_for_a, a_latest_header);
        //     assert!(client_msg_b_res.is_ok());
        //
        //     let client_msg_b = client_msg_b_res.unwrap();
        //     // Submit the datagram to chain B.
        //     let dispatch_res_b = chain_b.send(ICS26Envelope::ICS2Msg(client_msg_b));
        // }
    }
}
