use std::path::Path;

use crate::chain::cli::wasm_client::store_wasm_client_code;
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
}
