use crate::{
    chain::{
        cli::async_icq::{
            async_icq,
            update_oracle,
        },
        driver::ChainDriver,
    },
    error::Error,
    prelude::*,
    types::tagged::*,
};

pub trait AsyncIcqMethodsExt<Chain> {
    fn update_oracle(&self, relayer: &str, account: &str) -> Result<(), Error>;

    fn async_icq(&self, channel_id: &ChannelId, query_json: &str, from: &str) -> Result<(), Error>;
}

impl<'a, Chain: Send> AsyncIcqMethodsExt<Chain> for MonoTagged<Chain, &'a ChainDriver> {
    fn update_oracle(&self, relayer: &str, account: &str) -> Result<(), Error> {
        let driver = *self.value();
        update_oracle(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
            account,
            relayer,
        )
    }

    fn async_icq(&self, channel_id: &ChannelId, query_json: &str, from: &str) -> Result<(), Error> {
        let driver = *self.value();
        async_icq(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
            channel_id.as_str(),
            query_json,
            from,
        )
    }
}
