use crate::State;

use quote::quote;

impl State {
	pub fn impl_fn_height(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => state.height(),
			}
		});

		quote! {
			fn height(&self) -> Height {
				match self {
					#(#cases)*
				}
			}
		}
	}

	pub fn impl_header(&self) -> proc_macro2::TokenStream {
		let this = &self.self_ident;
		let gens = &self.generics;
		let gens_where = &self.generics.where_clause;

		let fn_height = self.impl_fn_height();
		let fn_downcast = self.impl_fn_downcast();
		let fn_wrap = self.impl_fn_wrap();
		let fn_encode_to_vec = self.impl_fn_encode_to_vec();

		quote! {
			impl #gens Header for #this #gens #gens_where {
				#fn_height
				#fn_downcast
				#fn_wrap
				#fn_encode_to_vec
			}
		}
	}
}
