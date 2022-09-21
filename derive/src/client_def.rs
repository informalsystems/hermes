use crate::State;
use quote::quote;

impl State {
	fn impl_fn_verify_client_message(&self) -> proc_macro2::TokenStream {
		let any_client_state = &self.any_data.client_state_ident;
		let any_client_message = &self.any_data.client_message_ident;
		let gen_params = &self.generics.params;
		let error = &self.current_impl_error;
		let crate_ = &self.crate_ident;
		let trait_ = &self.current_impl_trait;
		let client_state_trait = &self.client_state_trait;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = #client_state_trait::client_type(&client_state).to_owned();
					let (client_state, client_message) = #crate_::downcast!(
						client_state => #any_client_state::<#gen_params>::#variant_ident,
						client_message => #any_client_message::#variant_ident,
					)
					.ok_or_else(|| #error::client_args_type_mismatch(client_type))?;

					#trait_::verify_client_message::<Ctx>(client, ctx, client_id, client_state, client_message)
				}
			}
		});

		quote! {
			#[doc = "Validate an incoming client message"]
			fn verify_client_message<Ctx>(
				&self,
				ctx: &Ctx,
				client_id: #crate_::core::ics24_host::identifier::ClientId,
				client_state: Self::ClientState,
				client_message: Self::ClientMessage,
			) -> ::core::result::Result<(), #error>
			where
				Ctx: #crate_::core::ics26_routing::context::ReaderContext,
			{
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_update_state(&self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		let error = &self.current_impl_error;
		let trait_ = &self.current_impl_trait;
		let client_state_trait = &self.client_state_trait;
		let any_client_state = &self.any_data.client_state_ident;
		let any_client_message = &self.any_data.client_message_ident;
		let gen_params = &self.generics.params;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = #client_state_trait::client_type(&client_state).to_owned();
					let (client_state, client_message) = #crate_::downcast!(
						client_state => #any_client_state::<#gen_params>::#variant_ident,
						client_message => #any_client_message::#variant_ident,
					)
					.ok_or_else(|| #error::client_args_type_mismatch(client_type))?;

					let (new_state, new_consensus) =
						#trait_::update_state(client, ctx, client_id, client_state, client_message)?;

					Ok((Self::ClientState::#variant_ident(new_state), new_consensus))
				}
			}
		});

		quote! {
			#[doc = "Validates an incoming `client_message` against the latest consensus state of this client."]
			fn update_state<Ctx>(
				&self,
				ctx: &Ctx,
				client_id: #crate_::core::ics24_host::identifier::ClientId,
				client_state: Self::ClientState,
				client_message: Self::ClientMessage,
			) -> ::core::result::Result<(Self::ClientState, #crate_::core::ics02_client::client_def::ConsensusUpdateResult<Ctx>), #error>
			where
				Ctx: #crate_::core::ics26_routing::context::ReaderContext,
			{
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_update_state_on_misbehaviour(&self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		let trait_ = &self.current_impl_trait;
		let error = &self.current_impl_error;
		let any_client_state = &self.any_data.client_state_ident;
		let any_client_message = &self.any_data.client_message_ident;
		let gen_params = &self.generics.params;
		let client_state_trait = &self.client_state_trait;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = #client_state_trait::client_type(&client_state).to_owned();
					let (client_state, client_message) = #crate_::downcast!(
						client_state => #any_client_state::<#gen_params>::#variant_ident,
						client_message => #any_client_message::#variant_ident,
					)
					.ok_or_else(|| #error::client_args_type_mismatch(client_type))?;

					let client_state = #trait_::update_state_on_misbehaviour(client, client_state, client_message)?;
					Ok(Self::ClientState::#variant_ident(client_state))
				}
			}
		});

		quote! {
			fn update_state_on_misbehaviour(
				&self,
				client_state: Self::ClientState,
				client_message: Self::ClientMessage,
			) -> ::core::result::Result<Self::ClientState, #error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_check_for_misbehaviour(&self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		let error = &self.current_impl_error;
		let trait_ = &self.current_impl_trait;
		let client_state_trait = &self.client_state_trait;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = #client_state_trait::client_type(&client_state).to_owned();
					let (client_state, client_message) = #crate_::downcast!(
						client_state => Self::ClientState::#variant_ident,
						client_message => Self::ClientMessage::#variant_ident,
					)
					.ok_or_else(|| #error::client_args_type_mismatch(client_type))?;
					#trait_::check_for_misbehaviour(client, ctx, client_id, client_state, client_message)
				}
			}
		});

		quote! {
			#[doc = "Checks for misbehaviour in an incoming client_message"]
			fn check_for_misbehaviour<Ctx>(
				&self,
				ctx: &Ctx,
				client_id: #crate_::core::ics24_host::identifier::ClientId,
				client_state: Self::ClientState,
				client_message: Self::ClientMessage,
			) -> ::core::result::Result<bool, #error>
			where
				Ctx: #crate_::core::ics26_routing::context::ReaderContext,
			{
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_upgrade_and_update_state(&self) -> proc_macro2::TokenStream {
		let error = &self.current_impl_error;
		let crate_ = &self.crate_ident;
		let trait_ = &self.current_impl_trait;
		let client_state_trait = &self.client_state_trait;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = #client_state_trait::client_type(client_state).to_owned();
					let (client_state, consensus_state) = #crate_::downcast!(
						client_state => Self::ClientState::#variant_ident,
						consensus_state => Self::ConsensusState::#variant_ident,
					)
					.ok_or_else(|| #error::client_args_type_mismatch(client_type))?;

					let (new_state, new_consensus) = #trait_::verify_upgrade_and_update_state::<Ctx>(
						client,
						client_state,
						consensus_state,
						proof_upgrade_client,
						proof_upgrade_consensus_state,
					)?;

					Ok((Self::ClientState::#variant_ident(new_state), new_consensus))
				}
			}
		});

		quote! {
			fn verify_upgrade_and_update_state<Ctx: #crate_::core::ics26_routing::context::ReaderContext>(
				&self,
				client_state: &Self::ClientState,
				consensus_state: &Self::ConsensusState,
				proof_upgrade_client: ::alloc::vec::Vec<u8>,
				proof_upgrade_consensus_state: ::alloc::vec::Vec<u8>,
			) -> ::core::result::Result<(Self::ClientState, #crate_::core::ics02_client::client_def::ConsensusUpdateResult<Ctx>), #error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_client_consensus_state(&self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		let trait_ = &self.current_impl_trait;
		let error = &self.current_impl_error;
		let client_state_trait = &self.client_state_trait;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = #client_state_trait::client_type(client_state).to_owned();
					let client_state = #crate_::downcast!(
						client_state => Self::ClientState::#variant_ident
					)
					.ok_or_else(|| #error::client_args_type_mismatch(client_type))?;

					#trait_::verify_client_consensus_state(
						client,
						ctx,
						client_state,
						height,
						prefix,
						proof,
						root,
						client_id,
						consensus_height,
						expected_consensus_state,
					)
				}
			}
		});

		quote! {
			fn verify_client_consensus_state<Ctx: #crate_::core::ics26_routing::context::ReaderContext>(
				&self,
				ctx: &Ctx,
				client_state: &Self::ClientState,
				height: #crate_::core::ics02_client::height::Height,
				prefix: &#crate_::core::ics23_commitment::commitment::CommitmentPrefix,
				proof: &#crate_::core::ics23_commitment::commitment::CommitmentProofBytes,
				root: &#crate_::core::ics23_commitment::commitment::CommitmentRoot,
				client_id: &#crate_::core::ics24_host::identifier::ClientId,
				consensus_height: #crate_::core::ics02_client::height::Height,
				expected_consensus_state: &Ctx::AnyConsensusState,
			) -> ::core::result::Result<(), #error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_connection_state(&self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		let trait_ = &self.current_impl_trait;
		let error = &self.current_impl_error;
		let client_state_trait = &self.client_state_trait;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = #client_state_trait::client_type(client_state).to_owned();
					let client_state = #crate_::downcast!(client_state => Self::ClientState::#variant_ident)
						.ok_or_else(|| #error::client_args_type_mismatch(client_type))?;

					#trait_::verify_connection_state(
						client,
						ctx,
						client_id,
						client_state,
						height,
						prefix,
						proof,
						root,
						connection_id,
						expected_connection_end,
					)
				}
			}
		});

		quote! {
			fn verify_connection_state<Ctx: #crate_::core::ics26_routing::context::ReaderContext>(
				&self,
				ctx: &Ctx,
				client_id: &#crate_::core::ics24_host::identifier::ClientId,
				client_state: &Self::ClientState,
				height: #crate_::core::ics02_client::height::Height,
				prefix: &#crate_::core::ics23_commitment::commitment::CommitmentPrefix,
				proof: &#crate_::core::ics23_commitment::commitment::CommitmentProofBytes,
				root: &#crate_::core::ics23_commitment::commitment::CommitmentRoot,
				connection_id: &#crate_::core::ics24_host::identifier::ConnectionId,
				expected_connection_end: &#crate_::core::ics03_connection::connection::ConnectionEnd,
			) -> ::core::result::Result<(), #error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_channel_state(&self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		let trait_ = &self.current_impl_trait;
		let error = &self.current_impl_error;
		let client_state_trait = &self.client_state_trait;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = #client_state_trait::client_type(client_state).to_owned();
					let client_state = #crate_::downcast!(client_state => Self::ClientState::#variant_ident)
						.ok_or_else(|| #error::client_args_type_mismatch(client_type))?;

					#trait_::verify_channel_state(
						client,
						ctx,
						client_id,
						client_state,
						height,
						prefix,
						proof,
						root,
						port_id,
						channel_id,
						expected_channel_end,
					)
				}
			}
		});

		quote! {
			fn verify_channel_state<Ctx: #crate_::core::ics26_routing::context::ReaderContext>(
				&self,
				ctx: &Ctx,
				client_id: &#crate_::core::ics24_host::identifier::ClientId,
				client_state: &Self::ClientState,
				height: #crate_::core::ics02_client::height::Height,
				prefix: &#crate_::core::ics23_commitment::commitment::CommitmentPrefix,
				proof: &#crate_::core::ics23_commitment::commitment::CommitmentProofBytes,
				root: &#crate_::core::ics23_commitment::commitment::CommitmentRoot,
				port_id: &#crate_::core::ics24_host::identifier::PortId,
				channel_id: &#crate_::core::ics24_host::identifier::ChannelId,
				expected_channel_end: &#crate_::core::ics04_channel::channel::ChannelEnd,
			) -> ::core::result::Result<(), #error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_client_full_state(&self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		let trait_ = &self.current_impl_trait;
		let error = &self.current_impl_error;
		let client_state_trait = &self.client_state_trait;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = #client_state_trait::client_type(client_state).to_owned();
					let client_state = #crate_::downcast!(
						client_state => Self::ClientState::#variant_ident
					)
					.ok_or_else(|| #error::client_args_type_mismatch(client_type))?;

					#trait_::verify_client_full_state(
						client,
						ctx,
						client_state,
						height,
						prefix,
						proof,
						root,
						client_id,
						client_state_on_counterparty,
					)
				}
			}
		});

		quote! {
			fn verify_client_full_state<Ctx: #crate_::core::ics26_routing::context::ReaderContext>(
				&self,
				ctx: &Ctx,
				client_state: &Self::ClientState,
				height: #crate_::core::ics02_client::height::Height,
				prefix: &#crate_::core::ics23_commitment::commitment::CommitmentPrefix,
				proof: &#crate_::core::ics23_commitment::commitment::CommitmentProofBytes,
				root: &#crate_::core::ics23_commitment::commitment::CommitmentRoot,
				client_id: &#crate_::core::ics24_host::identifier::ClientId,
				client_state_on_counterparty: &Ctx::AnyClientState,
			) -> ::core::result::Result<(), #error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_packet_data(&self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		let trait_ = &self.current_impl_trait;
		let error = &self.current_impl_error;
		let client_state_trait = &self.client_state_trait;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = #client_state_trait::client_type(client_state).to_owned();
					let client_state = #crate_::downcast!(
						client_state => Self::ClientState::#variant_ident
					)
					.ok_or_else(|| #error::client_args_type_mismatch(client_type))?;

					#trait_::verify_packet_data(
						client,
						ctx,
						client_id,
						client_state,
						height,
						connection_end,
						proof,
						root,
						port_id,
						channel_id,
						sequence,
						commitment,
					)
				}
			}
		});

		quote! {
			fn verify_packet_data<Ctx: #crate_::core::ics26_routing::context::ReaderContext>(
				&self,
				ctx: &Ctx,
				client_id: &#crate_::core::ics24_host::identifier::ClientId,
				client_state: &Self::ClientState,
				height: #crate_::core::ics02_client::height::Height,
				connection_end: &#crate_::core::ics03_connection::connection::ConnectionEnd,
				proof: &#crate_::core::ics23_commitment::commitment::CommitmentProofBytes,
				root: &#crate_::core::ics23_commitment::commitment::CommitmentRoot,
				port_id: &#crate_::core::ics24_host::identifier::PortId,
				channel_id: &#crate_::core::ics24_host::identifier::ChannelId,
				sequence: #crate_::core::ics04_channel::packet::Sequence,
				commitment: #crate_::core::ics04_channel::commitment::PacketCommitment,
			) -> ::core::result::Result<(), #error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_packet_acknowledgement(&self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		let trait_ = &self.current_impl_trait;
		let error = &self.current_impl_error;
		let client_state_trait = &self.client_state_trait;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = #client_state_trait::client_type(client_state).to_owned();
					let client_state = #crate_::downcast!(
						client_state => Self::ClientState::#variant_ident
					)
					.ok_or_else(|| #error::client_args_type_mismatch(client_type))?;

					#trait_::verify_packet_acknowledgement(
						client,
						ctx,
						client_id,
						client_state,
						height,
						connection_end,
						proof,
						root,
						port_id,
						channel_id,
						sequence,
						ack_commitment,
					)
				}
			}
		});

		quote! {
			fn verify_packet_acknowledgement<Ctx: #crate_::core::ics26_routing::context::ReaderContext>(
				&self,
				ctx: &Ctx,
				client_id: &#crate_::core::ics24_host::identifier::ClientId,
				client_state: &Self::ClientState,
				height: #crate_::core::ics02_client::height::Height,
				connection_end: &#crate_::core::ics03_connection::connection::ConnectionEnd,
				proof: &#crate_::core::ics23_commitment::commitment::CommitmentProofBytes,
				root: &#crate_::core::ics23_commitment::commitment::CommitmentRoot,
				port_id: &#crate_::core::ics24_host::identifier::PortId,
				channel_id: &#crate_::core::ics24_host::identifier::ChannelId,
				sequence: #crate_::core::ics04_channel::packet::Sequence,
				ack_commitment: #crate_::core::ics04_channel::commitment::AcknowledgementCommitment,
			) -> ::core::result::Result<(), #error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_next_sequence_recv(&self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		let trait_ = &self.current_impl_trait;
		let error = &self.current_impl_error;
		let client_state_trait = &self.client_state_trait;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = #client_state_trait::client_type(client_state).to_owned();
					let client_state = #crate_::downcast!(
						client_state => Self::ClientState::#variant_ident
					)
					.ok_or_else(|| #error::client_args_type_mismatch(client_type))?;

					#trait_::verify_next_sequence_recv(
						client,
						ctx,
						client_id,
						client_state,
						height,
						connection_end,
						proof,
						root,
						port_id,
						channel_id,
						sequence,
					)
				}
			}
		});

		quote! {
			fn verify_next_sequence_recv<Ctx: #crate_::core::ics26_routing::context::ReaderContext>(
				&self,
				ctx: &Ctx,
				client_id: &#crate_::core::ics24_host::identifier::ClientId,
				client_state: &Self::ClientState,
				height: #crate_::core::ics02_client::height::Height,
				connection_end: &#crate_::core::ics03_connection::connection::ConnectionEnd,
				proof: &#crate_::core::ics23_commitment::commitment::CommitmentProofBytes,
				root: &#crate_::core::ics23_commitment::commitment::CommitmentRoot,
				port_id: &#crate_::core::ics24_host::identifier::PortId,
				channel_id: &#crate_::core::ics24_host::identifier::ChannelId,
				sequence: #crate_::core::ics04_channel::packet::Sequence,
			) -> ::core::result::Result<(), #error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_packet_receipt_absence(&self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		let trait_ = &self.current_impl_trait;
		let error = &self.current_impl_error;
		let client_state_trait = &self.client_state_trait;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			let _client_state_path = &client.client_state_path;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = #client_state_trait::client_type(client_state).to_owned();
					let client_state = #crate_::downcast!(
						client_state => Self::ClientState::#variant_ident
					)
					.ok_or_else(|| #error::client_args_type_mismatch(client_type))?;

					#trait_::verify_packet_receipt_absence(
						client,
						ctx,
						client_id,
						client_state,
						height,
						connection_end,
						proof,
						root,
						port_id,
						channel_id,
						sequence,
					)
				}
			}
		});

		quote! {
			fn verify_packet_receipt_absence<Ctx: #crate_::core::ics26_routing::context::ReaderContext>(
				&self,
				ctx: &Ctx,
				client_id: &#crate_::core::ics24_host::identifier::ClientId,
				client_state: &Self::ClientState,
				height: #crate_::core::ics02_client::height::Height,
				connection_end: &#crate_::core::ics03_connection::connection::ConnectionEnd,
				proof: &#crate_::core::ics23_commitment::commitment::CommitmentProofBytes,
				root: &#crate_::core::ics23_commitment::commitment::CommitmentRoot,
				port_id: &#crate_::core::ics24_host::identifier::PortId,
				channel_id: &#crate_::core::ics24_host::identifier::ChannelId,
				sequence: #crate_::core::ics04_channel::packet::Sequence,
			) -> ::core::result::Result<(), #error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	pub fn impl_client_def(&mut self) -> proc_macro2::TokenStream {
		let crate_ = &self.crate_ident;
		self.current_impl_trait =
			syn::parse2(quote! { #crate_::core::ics02_client::client_def::ClientDef }).unwrap();
		self.current_impl_error =
			syn::parse2(quote! { #crate_::core::ics02_client::error::Error }).unwrap();

		let this = &self.self_ident;
		let any_client_message = &self.any_data.client_message_ident;
		let any_client_state = &self.any_data.client_state_ident;
		let any_consensus_state = &self.any_data.consensus_state_ident;
		let client_def_trait = &self.current_impl_trait;
		let (impl_generics, ty_generics, where_clause) = self.generics.split_for_impl();

		let fn_verify_client_message = self.impl_fn_verify_client_message();
		let fn_update_state = self.impl_fn_update_state();
		let fn_update_state_on_misbehaviour = self.impl_fn_update_state_on_misbehaviour();
		let fn_check_for_misbehaviour = self.impl_fn_check_for_misbehaviour();
		let fn_verify_upgrade_and_update_state = self.impl_fn_verify_upgrade_and_update_state();
		let fn_verify_client_consensus_state = self.impl_fn_verify_client_consensus_state();
		let fn_verify_connection_state = self.impl_fn_verify_connection_state();
		let fn_verify_channel_state = self.impl_fn_verify_channel_state();
		let fn_verify_client_full_state = self.impl_fn_verify_client_full_state();
		let fn_verify_packet_data = self.impl_fn_verify_packet_data();
		let fn_verify_packet_acknowledgement = self.impl_fn_verify_packet_acknowledgement();
		let fn_verify_next_sequence_recv = self.impl_fn_verify_next_sequence_recv();
		let fn_verify_packet_receipt_absence = self.impl_fn_verify_packet_receipt_absence();

		quote! {
			impl #impl_generics #client_def_trait for #this #ty_generics #where_clause {
				type ClientMessage = #any_client_message;
				type ClientState = #any_client_state::<#ty_generics>;
				type ConsensusState = #any_consensus_state;

				#fn_verify_client_message
				#fn_update_state
				#fn_update_state_on_misbehaviour
				#fn_check_for_misbehaviour
				#fn_verify_upgrade_and_update_state
				#fn_verify_client_consensus_state
				#fn_verify_connection_state
				#fn_verify_channel_state
				#fn_verify_client_full_state
				#fn_verify_packet_data
				#fn_verify_packet_acknowledgement
				#fn_verify_next_sequence_recv
				#fn_verify_packet_receipt_absence
			}
		}
	}
}
