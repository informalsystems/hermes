use std::path::Path;

use crate::chain::cli::wasm::contract::{store_wasm_client_code, store_wasm_contract};
use crate::chain::driver::ChainDriver;
use crate::error::Error;
use crate::types::tagged::*;

pub trait StoreWasmClientCodeMethodsExt {
    fn store_wasm_client_code(
        &self,
        wasm_path: &Path,
        title: &str,
        summary: &str,
        signer: &str,
    ) -> Result<String, Error>;

    fn store_wasm_contract(
        &self,
        title: &str,
        summary: &str,
        wasm_file: &str,
        authority: &str,
        from: &str,
        deposit: &str,
        fees: &str,
        gas: &str,
    ) -> Result<String, Error>;
}

impl<'a, Chain: Send> StoreWasmClientCodeMethodsExt for MonoTagged<Chain, &'a ChainDriver> {
    fn store_wasm_client_code(
        &self,
        wasm_path: &Path,
        title: &str,
        summary: &str,
        signer: &str,
    ) -> Result<String, Error> {
        self.value()
            .store_wasm_client_code(wasm_path, title, summary, signer)
    }

    fn store_wasm_contract(
        &self,
        title: &str,
        summary: &str,
        wasm_file: &str,
        authority: &str,
        from: &str,
        deposit: &str,
        fees: &str,
        gas: &str,
    ) -> Result<String, Error> {
        self.value().store_wasm_contract(
            title, summary, wasm_file, authority, from, deposit, fees, gas,
        )
    }
}

impl StoreWasmClientCodeMethodsExt for ChainDriver {
    fn store_wasm_client_code(
        &self,
        wasm_path: &Path,
        title: &str,
        summary: &str,
        signer: &str,
    ) -> Result<String, Error> {
        store_wasm_client_code(self, wasm_path, title, summary, signer)
    }

    fn store_wasm_contract(
        &self,
        title: &str,
        summary: &str,
        wasm_file: &str,
        authority: &str,
        from: &str,
        deposit: &str,
        fees: &str,
        gas: &str,
    ) -> Result<String, Error> {
        store_wasm_contract(
            self, title, summary, wasm_file, authority, from, deposit, fees, gas,
        )
    }
}
