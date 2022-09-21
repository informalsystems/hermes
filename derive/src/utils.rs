// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use proc_macro2::Span;
use proc_macro_crate::{crate_name, FoundCrate};
use quote::quote;
use syn::parse::Error;
use syn::{Ident, Path, TypePath};

/// Generate the crate access for the crate using 2018 syntax.
///
/// for `ibc` output will for example be `ibc_rs`.
pub fn generate_crate_access_2018(def_crate: &str) -> Result<Path, Error> {
	if std::env::var("CARGO_PKG_NAME").unwrap() == def_crate {
		return Ok(Ident::new(&"crate", Span::call_site()).into());
	}
	match crate_name(def_crate) {
		Ok(FoundCrate::Itself) => {
			let path = Ident::new(&def_crate.to_string().replace("-", "_"), Span::call_site());
			Ok(syn::parse2(quote! { ::#path })?)
		},
		Ok(FoundCrate::Name(name)) => {
			let ident = Ident::new(&name, Span::call_site());
			Ok(syn::parse2(quote! { ::#ident })?)
		},
		Err(e) => Err(Error::new(Span::call_site(), e)),
	}
}

pub fn ident_path(ident: Ident) -> TypePath {
	let client_def_path = TypePath { qself: None, path: syn::Path::from(ident) };
	client_def_path
}
