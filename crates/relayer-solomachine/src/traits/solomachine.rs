use async_trait::async_trait;
use core::fmt::Debug;
use ibc_relayer_all_in_one::one_for_all::traits::runtime::OfaRuntime;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::logger::traits::level::HasBaseLogLevels;
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use prost::EncodeError;
use secp256k1::{PublicKey, SecretKey};

#[async_trait]
pub trait SolomachineChain: Async {
    type Error: Debug + Async;

    type Runtime: OfaRuntime;

    type Logger: HasBaseLogLevels;

    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime>;

    fn runtime_error(e: <Self::Runtime as OfaRuntime>::Error) -> Self::Error;

    fn logger(&self) -> &Self::Logger;

    fn encode_error(e: EncodeError) -> Self::Error;

    fn public_key(&self) -> &PublicKey;

    // TODO: remove secret key accessor and provide sign methods instead.
    // Doing so would allow multisig or have the private key stored outside
    // of the process, such as in HSM.
    fn secret_key(&self) -> &SecretKey;

    /// Generate a new diversifier string to be used for the next UpdateClient.
    /// We use a different diversifier for each IBC message, in order to
    /// avoid misbehavior being triggered in case if the solomachine double signs.
    async fn generate_diversifier(&self, current_diversifier: &str) -> Result<String, Self::Error>;

    async fn handle_receive_packet(&self, packet: &Packet) -> Result<Vec<u8>, Self::Error>;
}
