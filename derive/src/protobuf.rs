use crate::{generate_crate_access_2018, State};
use convert_case::{Case, Casing};

use quote::quote;

impl State {
	pub fn impl_try_from_any(&self) -> proc_macro2::TokenStream {
		let this = &self.self_ident;
		let (impl_generics, ty_generics, where_clause) = self.generics.split_for_impl();
		let crate_ = &self.crate_ident;
		let error = quote!(#crate_::core::ics02_client::error::Error);

		let cases = self.clients.iter().filter_map(|client| {
			let type_url = client.proto_ty_url.as_ref()?;
			let decode_err = client.proto_decode_error.clone().unwrap_or_else(|| {
				let string_without_any = &this.to_string()[3..];
				syn::parse_str(&format!("decode_raw_{}", string_without_any.to_case(Case::Snake)))
					.unwrap()
			});
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			let inner_ty = &client.inner_ty_path;
			Some(quote! {
				#(#attrs)*
				#type_url => Ok(Self::#variant_ident(
					<#inner_ty>::decode_vec(&value.value)
						.map_err(#error::#decode_err)?,
				)),
			})
		});
		let ibc_proto =
			generate_crate_access_2018("ibc-proto").expect("'ibc-proto' crate not found");
		let proto_any = quote! { #ibc_proto::google::protobuf::Any };

		// TODO: fix up error variants used in decoding
		quote! {
			impl #impl_generics ::core::convert::TryFrom<#proto_any> for #this #ty_generics #where_clause {
				type Error = #error;

				fn try_from(value: #proto_any) -> ::core::result::Result<Self, Self::Error> {
					match value.type_url.as_str() {
						"" => Err(#error::empty_consensus_state_response()),
						#(#cases)*
						_ => Err(#error::unknown_consensus_state_type(value.type_url)),
					}
				}
			}
		}
	}

	pub fn impl_from_self_for_any(&self) -> proc_macro2::TokenStream {
		let this = &self.self_ident;
		let gens = &self.generics;
		let gens_where = &self.generics.where_clause;
		let gen_params = &self.generics.params;
		let ibc_proto =
			generate_crate_access_2018("ibc-proto").expect("'ibc-proto' crate not found");
		let proto_any = quote! { #ibc_proto::google::protobuf::Any };

		let cases = self.clients.iter().filter_map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			let type_url = client.proto_ty_url.as_ref()?;
			Some(quote! {
				#(#attrs)*
				#this ::<#gen_params> ::#variant_ident(value) => #proto_any {
					type_url: ::alloc::string::ToString::to_string(&#type_url),
					value: value.encode_to_vec(),
				},
			})
		});

		quote! {
			impl #gens ::core::convert::From<#this #gens> for #proto_any #gens_where {
				fn from(value: #this #gens) -> Self {
					match value {
						#(#cases)*
					}
				}
			}
		}
	}

	pub fn impl_protobuf(&self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		let this = &self.self_ident;
		let (impl_generics, ty_generics, where_clause) = self.generics.split_for_impl();

		let impl_try_from_any = self.impl_try_from_any();
		let impl_from_self_for_any = self.impl_from_self_for_any();

		let ibc_proto =
			generate_crate_access_2018("ibc-proto").expect("'ibc-proto' crate not found");

		let proto_any = quote! { #ibc_proto::google::protobuf::Any };
		quote! {
			impl #impl_generics
				#crate_::protobuf::Protobuf<#proto_any>
			for #this #ty_generics #where_clause {}

			#impl_try_from_any

			#impl_from_self_for_any
		}
	}
}
