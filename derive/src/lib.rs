mod client_def;
mod client_state;
mod coercion;
mod consensus_state;
mod header;
mod misbehaviour;
mod protobuf;
mod utils;

use proc_macro::{Span, TokenStream};
use proc_macro2::Ident;
use quote::quote;

use crate::utils::{generate_crate_access_2018, ident_path};
use syn::{parse_macro_input, Data, DeriveInput, Generics, Path, Type, TypePath};

struct AnyData {
	pub client_message_ident: Ident,
	pub client_state_ident: Ident,
	pub consensus_state_ident: Ident,
}

struct ClientData {
	pub variant_ident: Ident,
	pub inner_ty_path: TypePath,
	pub client_state_path: TypePath,
	pub attrs: Vec<syn::Attribute>,
	pub proto_ty_url: Option<Ident>,
	pub proto_decode_error: Option<Ident>,
}

impl ClientData {
	pub fn new(
		variant_ident: Ident,
		inner_ty_path: TypePath,
		attrs: Vec<syn::Attribute>,
		proto_ty_url: Option<Ident>,
		proto_decode_error: Option<Ident>,
	) -> Self {
		let client_state_path =
			ident_path(Ident::new(&format!("{}ClientState", variant_ident), variant_ident.span()));
		Self {
			variant_ident,
			inner_ty_path,
			client_state_path,
			attrs,
			proto_ty_url,
			proto_decode_error,
		}
	}
}

struct State {
	pub any_data: AnyData,
	pub clients: Vec<ClientData>,
	pub self_ident: Ident,
	pub generics: Generics,
	pub crate_ident: Path,
	pub current_impl_trait: TypePath,
	pub current_impl_error: TypePath,
	pub client_state_trait: TypePath,
}

#[proc_macro_derive(ClientDef, attributes(ibc))]
pub fn derive_client_def(input: TokenStream) -> TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	let mut state = State::from_input(input, client_data_with_proto_attrs);
	state.impl_client_def().into()
}

#[proc_macro_derive(ClientState, attributes(ibc))]
pub fn derive_client_state(input: TokenStream) -> TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	let mut state = State::from_input(input, client_data_with_proto_attrs);
	state.impl_client_state().into()
}

#[proc_macro_derive(ConsensusState, attributes(ibc))]
pub fn derive_consensus_state(input: TokenStream) -> TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	let mut state = State::from_input(input, client_data_with_proto_attrs);
	state.impl_consensus_state().into()
}

#[proc_macro_derive(ClientMessage, attributes(ibc))]
pub fn derive_client_message(input: TokenStream) -> TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	let mut state = State::from_input(input, client_data_with_proto_attrs);
	state.impl_client_message().into()
}

#[proc_macro_derive(Misbehaviour, attributes(ibc))]
pub fn derive_misbehaviour(input: TokenStream) -> TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	let mut state = State::from_input(input, client_data_with_proto_attrs);
	state.impl_misbehaviour().into()
}

#[proc_macro_derive(Protobuf, attributes(ibc))]
pub fn derive_protobuf(input: TokenStream) -> TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	let state = State::from_input(input, client_data_with_proto_attrs);
	state.impl_protobuf().into()
}

fn client_data_with_proto_attrs(variant: &syn::Variant) -> ClientData {
	assert_eq!(variant.fields.len(), 1, "Only single field variants are supported");
	let field = variant.fields.iter().next().unwrap();
	let client_def_path = match &field.ty {
		Type::Path(p) => p.clone(),
		_ => panic!("Only path types are supported"),
	};
	let mut proto_url = None;
	let mut proto_decode_error = None;
	let attrs = variant
		.attrs
		.iter()
		.filter(|attr| {
			let string = format!("{}", attr.path.segments.first().unwrap().ident);
			if string == "ibc" {
				let meta = attr.parse_meta().unwrap();
				if let syn::Meta::List(list) = meta {
					for nested in list.nested {
						if let syn::NestedMeta::Meta(syn::Meta::NameValue(nv)) = nested {
							let ident = &nv.path.segments.first().unwrap().ident;
							if let syn::Lit::Str(lit) = nv.lit {
								if ident == "proto_url" {
									assert!(
										proto_url.is_none(),
										"Only one proto type url is allowed"
									);
									proto_url = Some(Ident::new(&lit.value(), lit.span()));
								} else if ident == "proto_decode_err" {
									assert!(
										proto_decode_error.is_none(),
										"Only one proto decode error is allowed"
									);
									proto_decode_error = Some(Ident::new(&lit.value(), lit.span()));
								}
							}
						}
					}
				}
			}
			string == "cfg"
		})
		.cloned()
		.collect();

	ClientData::new(variant.ident.clone(), client_def_path, attrs, proto_url, proto_decode_error)
}

impl State {
	fn from_input(input: DeriveInput, client_fn: impl Fn(&syn::Variant) -> ClientData) -> Self {
		let data = match &input.data {
			Data::Enum(data) => data,
			_ => panic!("Only enums are supported"),
		};
		let span = input.ident.span();
		let crate_ = generate_crate_access_2018("ibc").expect("ibc-rs crate not found");
		let client_state_trait =
			syn::parse2(quote! { #crate_::core::ics02_client::client_state::ClientState }).unwrap();
		State {
			self_ident: input.ident,
			any_data: AnyData {
				client_message_ident: Ident::new("AnyClientMessage", span),
				client_state_ident: Ident::new("AnyClientState", span),
				consensus_state_ident: Ident::new("AnyConsensusState", span),
			},
			clients: data.variants.iter().map(client_fn).collect(),
			generics: input.generics.clone(),
			crate_ident: crate_,
			current_impl_trait: ident_path(Ident::new("UNKNOWN_TRAIT", Span::mixed_site().into())),
			current_impl_error: ident_path(Ident::new("UNKNOWN_ERROR", Span::mixed_site().into())),
			client_state_trait,
		}
	}
}
