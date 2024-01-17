use crate::{
    chain::cli::fee_grant::feegrant_grant,
    error::Error,
    prelude::{
        ChainDriver,
        TaggedTokenRef,
    },
    types::tagged::MonoTagged,
};
pub trait FeeGrantMethodsExt<Chain> {
    fn feegrant_grant(
        &self,
        granter: &str,
        grantee: &str,
        fees: &TaggedTokenRef<Chain>,
    ) -> Result<(), Error>;
}

impl<'a, Chain: Send> FeeGrantMethodsExt<Chain> for MonoTagged<Chain, &'a ChainDriver> {
    fn feegrant_grant(
        &self,
        granter: &str,
        grantee: &str,
        fees: &TaggedTokenRef<Chain>,
    ) -> Result<(), Error> {
        feegrant_grant(
            self.value().chain_id.as_str(),
            &self.value().command_path,
            &self.value().home_path,
            &self.value().rpc_listen_address(),
            granter,
            grantee,
            &fees.value().to_string(),
        )
    }
}
