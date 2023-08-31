use eyre::eyre;
use std::thread;
use std::time::Duration;

use ibc_relayer::chain::counterparty::unreceived_acknowledgements;
use ibc_relayer::chain::handle::{BaseChainHandle, ChainHandle};
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::path::PathIdentifiers;
use ibc_relayer_all_in_one::one_for_all::traits::birelay::OfaBiRelay;
use ibc_relayer_all_in_one::one_for_all::types::birelay::OfaBiRelayWrapper;
use ibc_relayer_components::relay::traits::auto_relayer::CanAutoRelay;
use ibc_relayer_cosmos::contexts::birelay::CosmosBiRelay;
use ibc_relayer_types::core::ics04_channel::channel::IdentifiedChannelEnd;
use tokio::task::JoinHandle;

use crate::error::Error;
use crate::framework::next::chain::{
    CanShutdown, CanSpawnRelayer, CanWaitForAck, HasContextId, HasTestConfig, HasTwoChains,
    HasTwoChannels, HasTwoNodes,
};
use crate::prelude::{
    assert_eventually_succeed, ConnectedChains, ConnectedChannel, FullNode, RelayerDriver,
    TestConfig,
};
use crate::types::tagged::*;
use crate::util::suspend::hang_on_error;

const WAIT_PENDING_ACKS_ATTEMPTS: u16 = 90;

/// Test context for the current relayer.
/// Uses a RelayerDriver.
pub struct TestContextV1<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub context_id: String,
    pub config: TestConfig,
    pub relayer: RelayerDriver,
    pub chains: ConnectedChains<ChainA, ChainB>,
    pub channel: ConnectedChannel<ChainA, ChainB>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTwoChains for TestContextV1<ChainA, ChainB> {
    type ChainA = ChainA;

    type ChainB = ChainB;

    fn chain_a(&self) -> &Self::ChainA {
        self.chains.handle_a()
    }

    fn chain_b(&self) -> &Self::ChainB {
        self.chains.handle_b()
    }

    fn foreign_client_a_to_b(&self) -> &ForeignClient<Self::ChainB, Self::ChainA> {
        &self.chains.foreign_clients.client_a_to_b
    }

    fn foreign_client_b_to_a(&self) -> &ForeignClient<Self::ChainA, Self::ChainB> {
        &self.chains.foreign_clients.client_b_to_a
    }

    fn chains(&self) -> &ConnectedChains<Self::ChainA, Self::ChainB> {
        &self.chains
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTwoNodes for TestContextV1<ChainA, ChainB> {
    fn node_a(&self) -> &MonoTagged<Self::ChainA, FullNode> {
        &self.chains.node_a
    }

    fn node_b(&self) -> &MonoTagged<Self::ChainB, FullNode> {
        &self.chains.node_b
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTestConfig for TestContextV1<ChainA, ChainB> {
    fn config(&self) -> &TestConfig {
        &self.config
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTwoChannels for TestContextV1<ChainA, ChainB> {
    fn channel(&self) -> &ConnectedChannel<Self::ChainA, Self::ChainB> {
        &self.channel
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> CanSpawnRelayer for TestContextV1<ChainA, ChainB> {
    fn spawn_relayer(&self) -> Result<Option<JoinHandle<()>>, Error> {
        let relayer = self.relayer.clone();
        thread::spawn(move || {
            if let Ok(handler) = relayer.spawn_supervisor() {
                handler.wait();
            }
        });

        Ok(None)
    }

    fn with_supervisor<R>(&self, cont: impl FnOnce() -> Result<R, Error>) -> Result<R, Error> {
        self.relayer.with_supervisor(cont)
    }
}

pub fn wait_for_acks<Chain, Counterparty>(
    chain: &Chain,
    counterparty: &Counterparty,
    path_identifiers: &PathIdentifiers,
) -> Result<(), Error>
where
    Chain: ChainHandle,
    Counterparty: ChainHandle,
{
    assert_eventually_succeed(
        "waiting on pending acks on chain",
        WAIT_PENDING_ACKS_ATTEMPTS,
        Duration::from_secs(1),
        || {
            let unreceived_acks =
                unreceived_acknowledgements(chain, counterparty, path_identifiers);

            match unreceived_acks {
                Ok(Some((acks, _))) => {
                    if acks.is_empty() {
                        Ok(())
                    } else {
                        Err(Error::generic(eyre!(
                            "there are still {} pending acks",
                            acks.len()
                        )))
                    }
                }
                Ok(None) => Ok(()),
                Err(e) => Err(Error::generic(eyre!(
                    "error retrieving number of pending acks {}",
                    e
                ))),
            }
        },
    )
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> CanWaitForAck for TestContextV1<ChainA, ChainB> {
    fn wait_for_src_acks(&self) -> Result<(), Error> {
        let src_chain = self.chain_a();
        let dst_chain = self.chain_b();
        let channel = self.channel();

        let channel_end_a = match channel.channel.a_channel(Some(&channel.channel_id_a.0)) {
            Ok(channel_end) => channel_end,
            Err(e) => {
                return Err(e.into());
            }
        };
        let identified_channel_end_a = IdentifiedChannelEnd::new(
            channel.port_a.0.clone(),
            channel.channel_id_a.0.clone(),
            channel_end_a,
        );
        let path_identifiers_a =
            match PathIdentifiers::from_channel_end(identified_channel_end_a.clone()) {
                Some(path_identifiers) => path_identifiers,
                None => {
                    return Err(Error::generic(eyre!(
                        "No path identifier found for {:?}",
                        identified_channel_end_a
                    )));
                }
            };

        wait_for_acks(src_chain, dst_chain, &path_identifiers_a)?;

        Ok(())
    }

    fn wait_for_dst_acks(&self) -> Result<(), Error> {
        let src_chain = self.chain_a();
        let dst_chain = self.chain_b();
        let channel = self.channel();
        let channel_end_b = match channel.channel.b_channel(Some(&channel.channel_id_b.0)) {
            Ok(channel_end) => channel_end,
            Err(e) => {
                return Err(e.into());
            }
        };
        let identified_channel_end_b = IdentifiedChannelEnd::new(
            channel.port_b.0.clone(),
            channel.channel_id_b.0.clone(),
            channel_end_b,
        );
        let path_identifiers_b =
            match PathIdentifiers::from_channel_end(identified_channel_end_b.clone()) {
                Some(path_identifiers) => path_identifiers,
                None => {
                    tracing::error!(
                        "{}",
                        Error::generic(eyre!("error getting path_identifiers b"))
                    );
                    return Err(Error::generic(eyre!(
                        "No path identifier found for {:?}",
                        identified_channel_end_b
                    )));
                }
            };

        wait_for_acks(dst_chain, src_chain, &path_identifiers_b)?;

        Ok(())
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> CanShutdown for TestContextV1<ChainA, ChainB> {
    fn shutdown(&self, _auto_relay_handle: Option<JoinHandle<()>>) {}
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasContextId for TestContextV1<ChainA, ChainB> {
    fn context_id(&self) -> String {
        self.context_id.clone()
    }
}

/// Test context for the relayer-next.
/// Uses a OfaBiRelayWrapper.
pub struct TestContextV2<ChainA: ChainHandle, ChainB: ChainHandle> {
    pub context_id: String,
    pub config: TestConfig,
    pub relayer: OfaBiRelayWrapper<CosmosBiRelay<BaseChainHandle, BaseChainHandle>>,
    pub chains: ConnectedChains<ChainA, ChainB>,
    pub channel: ConnectedChannel<ChainA, ChainB>,
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTwoChains for TestContextV2<ChainA, ChainB> {
    type ChainA = ChainA;

    type ChainB = ChainB;

    fn chain_a(&self) -> &Self::ChainA {
        self.chains.handle_a()
    }

    fn chain_b(&self) -> &Self::ChainB {
        self.chains.handle_b()
    }

    fn foreign_client_a_to_b(&self) -> &ForeignClient<Self::ChainB, Self::ChainA> {
        &self.chains.foreign_clients.client_a_to_b
    }

    fn foreign_client_b_to_a(&self) -> &ForeignClient<Self::ChainA, Self::ChainB> {
        &self.chains.foreign_clients.client_b_to_a
    }

    fn chains(&self) -> &ConnectedChains<Self::ChainA, Self::ChainB> {
        &self.chains
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTwoNodes for TestContextV2<ChainA, ChainB> {
    fn node_a(&self) -> &MonoTagged<Self::ChainA, FullNode> {
        &self.chains.node_a
    }

    fn node_b(&self) -> &MonoTagged<Self::ChainB, FullNode> {
        &self.chains.node_b
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTestConfig for TestContextV2<ChainA, ChainB> {
    fn config(&self) -> &TestConfig {
        &self.config
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasTwoChannels for TestContextV2<ChainA, ChainB> {
    fn channel(&self) -> &ConnectedChannel<Self::ChainA, Self::ChainB> {
        &self.channel
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> CanSpawnRelayer for TestContextV2<ChainA, ChainB> {
    fn spawn_relayer(&self) -> Result<Option<JoinHandle<()>>, Error> {
        let runtime = self.relayer.birelay.runtime();
        let birelay = self.relayer.clone();

        let handle = runtime.runtime.spawn(async move {
            let _ = birelay.auto_relay().await;
        });

        Ok(Some(handle))
    }

    fn with_supervisor<R>(&self, cont: impl FnOnce() -> Result<R, Error>) -> Result<R, Error> {
        self.spawn_relayer()?;

        hang_on_error(false, cont)
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> CanWaitForAck for TestContextV2<ChainA, ChainB> {
    fn wait_for_src_acks(&self) -> Result<(), Error> {
        let src_chain = self.chain_a();
        let dst_chain = self.chain_b();
        let channel = self.channel();

        let channel_end_a = match channel.channel.a_channel(Some(&channel.channel_id_a.0)) {
            Ok(channel_end) => channel_end,
            Err(e) => {
                return Err(e.into());
            }
        };
        let identified_channel_end_a = IdentifiedChannelEnd::new(
            channel.port_a.0.clone(),
            channel.channel_id_a.0.clone(),
            channel_end_a,
        );
        let path_identifiers_a =
            match PathIdentifiers::from_channel_end(identified_channel_end_a.clone()) {
                Some(path_identifiers) => path_identifiers,
                None => {
                    return Err(Error::generic(eyre!(
                        "No path identifier found for {:?}",
                        identified_channel_end_a
                    )));
                }
            };

        wait_for_acks(src_chain, dst_chain, &path_identifiers_a)?;

        Ok(())
    }

    fn wait_for_dst_acks(&self) -> Result<(), Error> {
        let src_chain = self.chain_a();
        let dst_chain = self.chain_b();
        let channel = self.channel();
        let channel_end_b = match channel.channel.b_channel(Some(&channel.channel_id_b.0)) {
            Ok(channel_end) => channel_end,
            Err(e) => {
                return Err(e.into());
            }
        };
        let identified_channel_end_b = IdentifiedChannelEnd::new(
            channel.port_b.0.clone(),
            channel.channel_id_b.0.clone(),
            channel_end_b,
        );
        let path_identifiers_b =
            match PathIdentifiers::from_channel_end(identified_channel_end_b.clone()) {
                Some(path_identifiers) => path_identifiers,
                None => {
                    tracing::error!(
                        "{}",
                        Error::generic(eyre!("error getting path_identifiers b"))
                    );
                    return Err(Error::generic(eyre!(
                        "No path identifier found for {:?}",
                        identified_channel_end_b
                    )));
                }
            };

        wait_for_acks(dst_chain, src_chain, &path_identifiers_b)?;

        Ok(())
    }
}

/// This is a temporary solution. When the clean shutdown is implemented in the runtime
/// context, this should be replaced, see <https://github.com/informalsystems/hermes/issues/3245>.
impl<ChainA: ChainHandle, ChainB: ChainHandle> CanShutdown for TestContextV2<ChainA, ChainB> {
    fn shutdown(&self, auto_relay_handle: Option<JoinHandle<()>>) {
        if let Some(handle) = auto_relay_handle {
            JoinHandle::abort(&handle);
            loop {
                if handle.is_finished() {
                    break;
                }
                thread::sleep(Duration::from_secs(1));
            }
        }
    }
}

impl<ChainA: ChainHandle, ChainB: ChainHandle> HasContextId for TestContextV2<ChainA, ChainB> {
    fn context_id(&self) -> String {
        self.context_id.clone()
    }
}
