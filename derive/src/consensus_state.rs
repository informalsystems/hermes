use crate::State;

use quote::quote;

impl State {
	fn impl_fn_root(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => state.root(),
			}
		});

		quote! {
			fn root(&self) -> &CommitmentRoot {
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
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => state.timestamp(),
			}
		});

		quote! {
			fn timestamp(&self) -> Timestamp {
				match self {
					#(#cases)*
				}
			}
		}
	}

	pub fn impl_consensus_state(&self) -> proc_macro2::TokenStream {
		let this = &self.self_ident;
		let gens = &self.generics;
		let gens_where = &self.generics.where_clause;

		let fn_root = self.impl_fn_root();
		let fn_timestamp = self.impl_fn_timestamp();
		let fn_downcast = self.impl_fn_downcast();
		let fn_wrap = self.impl_fn_wrap();
		let fn_encode_to_vec = self.impl_fn_encode_to_vec();

		quote! {
			impl #gens ConsensusState for #this #gens #gens_where {
				type Error = Infallible;

				#fn_root
				#fn_timestamp
				#fn_downcast
				#fn_wrap
				#fn_encode_to_vec
			}
		}
	}
}
