use crate::State;

use quote::quote;

impl State {
	fn impl_fn_chain_id(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let trait_ = &self.current_impl_trait;
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => #trait_::chain_id(state),
			}
		});

		let crate_ = &self.crate_ident;
		quote! {
			fn chain_id(&self) -> #crate_::core::ics24_host::identifier::ChainId {
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
			let trait_ = &self.current_impl_trait;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => AnyClient::#variant_ident(#trait_::client_def(state)),
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
			let trait_ = &self.current_impl_trait;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => #trait_::client_type(state),
			}
		});

		let crate_ = &self.crate_ident;
		quote! {
			fn client_type(&self) -> #crate_::core::ics02_client::client_state::ClientType {
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
			let trait_ = &self.current_impl_trait;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => #trait_::latest_height(state),
			}
		});

		let crate_ = &self.crate_ident;
		quote! {
			fn latest_height(&self) -> #crate_::core::ics02_client::height::Height {
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
			let trait_ = &self.current_impl_trait;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => #trait_::frozen_height(state),
			}
		});

		let crate_ = &self.crate_ident;
		quote! {
			fn frozen_height(&self) -> ::core::option::Option<#crate_::core::ics02_client::height::Height> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_upgrade(&self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			let trait_ = &self.current_impl_trait;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => {
					let upgrade_options = #crate_::downcast!(upgrade_options => Self::UpgradeOptions::#variant_ident)
						.expect(&format!("upgrade options should be {}", stringify!(#variant_ident)));

					Self::#variant_ident(#trait_::upgrade(
						state,
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
				upgrade_height: #crate_::core::ics02_client::height::Height,
				upgrade_options: Self::UpgradeOptions,
				chain_id: #crate_::core::ics24_host::identifier::ChainId,
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
			let trait_ = &self.current_impl_trait;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => #trait_::expired(state, elapsed),
			}
		});

		quote! {
			fn expired(&self, elapsed: ::core::time::Duration) -> bool {
				match self {
					#(#cases)*
				}
			}
		}
	}

	pub fn impl_client_state(&mut self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		self.current_impl_trait =
			syn::parse2(quote! { #crate_::core::ics02_client::client_state::ClientState }).unwrap();
		self.current_impl_error =
			syn::parse2(quote! { #crate_::core::ics02_client::error::Error }).unwrap();

		let this = &self.self_ident;
		let (impl_generics, ty_generics, where_clause) = self.generics.split_for_impl();

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
		let current_impl_trait = &self.current_impl_trait;

		quote! {
			impl #impl_generics #current_impl_trait for #this #ty_generics #where_clause {
				type UpgradeOptions = AnyUpgradeOptions; // TODO: make variable?
				type ClientDef = AnyClient #ty_generics;

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
