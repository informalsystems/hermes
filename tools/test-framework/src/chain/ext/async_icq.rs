use crate::chain::cli::async_icq::{async_icq, update_oracle};
use crate::chain::cli::wasm::contract::instantiate_wasm_contract;
use crate::chain::cli::wasm::query::{query_wasm_list_code, query_wasm_list_contracts_by_code};
use crate::prelude::*;
use crate::types::tagged::*;

pub trait AsyncIcqMethodsExt<Chain> {
    fn update_oracle(&self, relayer: &str, fees: &str, init_args: &str) -> Result<(), Error>;

    fn async_icq(&self, channel_id: &ChannelId, query_json: &str, from: &str) -> Result<(), Error>;
}

impl<'a, Chain: Send> AsyncIcqMethodsExt<Chain> for MonoTagged<Chain, &'a ChainDriver> {
    fn update_oracle(&self, relayer: &str, fees: &str, init_args: &str) -> Result<(), Error> {
        let driver = *self.value();

        let wasm_code = query_wasm_list_code(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
        )?;

        instantiate_wasm_contract(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
            relayer,
            fees,
            &wasm_code,
            init_args,
        )?;

        let address = query_wasm_list_contracts_by_code(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
            &wasm_code,
        )?;

        update_oracle(
            driver.chain_id.as_str(),
            &driver.command_path,
            &driver.home_path,
            &driver.rpc_listen_address(),
            &address,
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
