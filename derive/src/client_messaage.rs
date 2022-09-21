use crate::State;

use quote::quote;

impl State {
	pub fn impl_fn_height(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			let trait_ = &self.current_impl_trait;
			quote! {
				#(#attrs)*
				Self::#variant_ident(state) => #trait_::height(state),
			}
		});

		let crate_ = &self.crate_ident;
		quote! {
			fn height(&self) -> #crate_::core::ics02_client::height::Height {
				match self {
					#(#cases)*
				}
			}
		}
	}

	pub fn impl_client_message(&mut self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		let this = &self.self_ident;
		self.current_impl_trait =
			syn::parse2(quote! { #crate_::core::ics02_client::client_message::ClientMessage })
				.unwrap();
		self.current_impl_error =
			syn::parse2(quote! { #crate_::core::ics02_client::error::Error }).unwrap();
		let trait_ = &self.current_impl_trait;

		let (impl_generics, ty_generics, where_clause) = self.generics.split_for_impl();

		let fn_downcast = self.impl_fn_downcast();
		let fn_wrap = self.impl_fn_wrap();
		let fn_encode_to_vec = self.impl_fn_encode_to_vec();

		quote! {
			impl #impl_generics #trait_ for #this #ty_generics #where_clause {
				#fn_downcast
				#fn_wrap
				#fn_encode_to_vec
			}
		}
	}
}
