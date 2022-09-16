use crate::State;
use convert_case::{Case, Casing};

use quote::quote;

impl State {
	pub fn impl_try_from_any(&self) -> proc_macro2::TokenStream {
		let this = &self.self_ident;
		let gens = &self.generics;
		let gens_where = &self.generics.where_clause;

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
						.map_err(Error::#decode_err)?,
				)),
			})
		});

		// TODO: fix up error variants used in decoding
		quote! {
			impl #gens TryFrom<Any> for #this #gens #gens_where {
				type Error = Error;

				fn try_from(value: Any) -> Result<Self, Self::Error> {
					match value.type_url.as_str() {
						"" => Err(Error::empty_consensus_state_response()),
						#(#cases)*
						_ => Err(Error::unknown_consensus_state_type(value.type_url)),
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

		let cases = self.clients.iter().filter_map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			let type_url = client.proto_ty_url.as_ref()?;
			Some(quote! {
				#(#attrs)*
				#this ::<#gen_params> ::#variant_ident(value) => Any {
					type_url: #type_url.to_string(),
					value: value.encode_to_vec(),
				},
			})
		});

		quote! {
			impl #gens From<#this #gens> for Any #gens_where {
				fn from(value: #this #gens) -> Self {
					match value {
						#(#cases)*
					}
				}
			}
		}
	}

	pub fn impl_protobuf(&self) -> proc_macro2::TokenStream {
		let this = &self.self_ident;
		let gens = &self.generics;
		let gens_where = &self.generics.where_clause;

		let impl_try_from_any = self.impl_try_from_any();
		let impl_from_self_for_any = self.impl_from_self_for_any();

		quote! {
			impl #gens Protobuf<Any> for #this #gens #gens_where {}

			#impl_try_from_any

			#impl_from_self_for_any
		}
	}
}
