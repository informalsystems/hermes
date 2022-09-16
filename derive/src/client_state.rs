use crate::State;

use quote::quote;

impl State {
	fn impl_fn_chain_id(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => state.chain_id(),
			}
		});

		quote! {
			fn chain_id(&self) -> ChainId {
				match self {
					#(#cases)*
				}
			}
		}
	}

	pub fn impl_fn_client_def(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => AnyClient::#variant_ident(state.client_def()),
			}
		});

		quote! {
			fn client_def(&self) -> Self::ClientDef {
				match self {
					#(#cases)*
				}
			}
		}
	}

	pub fn impl_fn_client_type(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => state.client_type(),
			}
		});

		quote! {
			fn client_type(&self) -> ClientType {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_latest_height(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => state.latest_height(),
			}
		});

		quote! {
			fn latest_height(&self) -> Height {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_frozen_height(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => state.frozen_height(),
			}
		});

		quote! {
			fn frozen_height(&self) -> Option<Height> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_upgrade(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => {
					let upgrade_options = downcast!(upgrade_options => Self::UpgradeOptions::#variant_ident)
						.expect(&format!("upgrade options should be {}", stringify!(#variant_ident)));

					Self::#variant_ident(state.upgrade(
						upgrade_height,
						upgrade_options,
						chain_id,
					))
				}
			}
		});

		quote! {
			fn upgrade(
				self,
				upgrade_height: Height,
				upgrade_options: Self::UpgradeOptions,
				chain_id: ChainId,
			) -> Self {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_expired(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => state.expired(elapsed),
			}
		});

		quote! {
			fn expired(&self, elapsed: Duration) -> bool {
				match self {
					#(#cases)*
				}
			}
		}
	}

	pub fn impl_client_state(&self) -> proc_macro2::TokenStream {
		let this = &self.self_ident;
		let gens = &self.generics;
		let gens_where = &self.generics.where_clause;

		let fn_chain_id = self.impl_fn_chain_id();
		let fn_client_type = self.impl_fn_client_type();
		let fn_client_def = self.impl_fn_client_def();
		let fn_latest_height = self.impl_fn_latest_height();
		let fn_frozen_height = self.impl_fn_frozen_height();
		let fn_upgrade = self.impl_fn_upgrade();
		let fn_expired = self.impl_fn_expired();
		let fn_downcast = self.impl_fn_downcast();
		let fn_wrap = self.impl_fn_wrap();
		let fn_encode_to_vec = self.impl_fn_encode_to_vec();

		quote! {
			impl #gens ClientState for #this #gens #gens_where {
				type UpgradeOptions = AnyUpgradeOptions; // TODO: make variable?
				type ClientDef = AnyClient #gens;

				#fn_chain_id
				#fn_client_type
				#fn_client_def
				#fn_latest_height
				#fn_frozen_height
				#fn_upgrade
				#fn_expired
				#fn_downcast
				#fn_wrap
				#fn_encode_to_vec
			}
		}
	}
}
