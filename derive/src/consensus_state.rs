use crate::State;

use quote::quote;

impl State {
	fn impl_fn_root(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			let trait_ = &self.current_impl_trait;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => #trait_::root(state),
			}
		});

		let crate_ = &self.crate_ident;
		quote! {
			fn root(&self) -> &#crate_::core::ics23_commitment::commitment::CommitmentRoot {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_timestamp(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			let trait_ = &self.current_impl_trait;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => #trait_::timestamp(state),
			}
		});

		let crate_ = &self.crate_ident;
		quote! {
			fn timestamp(&self) -> #crate_::timestamp::Timestamp {
				match self {
					#(#cases)*
				}
			}
		}
	}

	pub fn impl_consensus_state(&mut self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		self.current_impl_trait =
			syn::parse2(quote! { #crate_::core::ics02_client::client_consensus::ConsensusState })
				.unwrap();
		self.current_impl_error =
			syn::parse2(quote! { #crate_::core::ics02_client::error::Error }).unwrap();

		let this = &self.self_ident;
		let (impl_generics, ty_generics, where_clause) = self.generics.split_for_impl();
		let trait_ = &self.current_impl_trait;

		let fn_root = self.impl_fn_root();
		let fn_timestamp = self.impl_fn_timestamp();
		let fn_downcast = self.impl_fn_downcast();
		let fn_wrap = self.impl_fn_wrap();
		let fn_encode_to_vec = self.impl_fn_encode_to_vec();

		quote! {
			impl #impl_generics #trait_ for #this #ty_generics #where_clause {
				type Error = ::core::convert::Infallible;

				#fn_root
				#fn_timestamp
				#fn_downcast
				#fn_wrap
				#fn_encode_to_vec
			}
		}
	}
}
