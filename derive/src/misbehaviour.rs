use crate::State;

use quote::quote;

impl State {
	pub fn impl_fn_client_id(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			let trait_ = &self.current_impl_trait;
			quote! {
				#(#attrs)*
				Self::#variant_ident(misbehaviour) => #trait_::client_id(misbehaviour),
			}
		});

		let crate_ = &self.crate_ident;
		quote! {
			fn client_id(&self) -> &#crate_::core::ics24_host::identifier::ClientId {
				match self {
					#(#cases)*
				}
			}
		}
	}

	pub fn impl_misbehaviour(&mut self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		self.current_impl_trait =
			syn::parse2(quote! { #crate_::core::ics02_client::misbehaviour::Misbehaviour })
				.unwrap();
		self.current_impl_error =
			syn::parse2(quote! { #crate_::core::ics02_client::error::Error }).unwrap();
		let this = &self.self_ident;
		let trait_ = &self.current_impl_trait;
		let (impl_generics, ty_generics, where_clause) = self.generics.split_for_impl();

		let fn_client_id = self.impl_fn_client_id();
		let fn_height = self.impl_fn_height();
		let fn_downcast = self.impl_fn_downcast();
		let fn_wrap = self.impl_fn_wrap();
		let fn_encode_to_vec = self.impl_fn_encode_to_vec();

		quote! {
			impl #impl_generics #trait_ for #this #ty_generics #where_clause {
				#fn_client_id
				#fn_height
				#fn_downcast
				#fn_wrap
				#fn_encode_to_vec
			}
		}
	}
}
