use crate::State;
use quote::quote;

impl State {
	fn impl_fn_verify_header(&self) -> proc_macro2::TokenStream {
		let any_client_state = &self.any_data.client_state_ident;
		let any_header = &self.any_data.header_ident;
		let gen_params = &self.generics.params;

		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = client_state.client_type().to_owned();
					let (client_state, header) = downcast!(
						client_state => #any_client_state::<#gen_params>::#variant_ident,
						header => #any_header::#variant_ident,
					)
					.ok_or_else(|| Error::client_args_type_mismatch(client_type))?;

					client.verify_header::<Ctx>(ctx, client_id, client_state, header)
				}
			}
		});

		quote! {
			#[doc = "Validate an incoming header"]
			fn verify_header<Ctx>(
				&self,
				ctx: &Ctx,
				client_id: ClientId,
				client_state: Self::ClientState,
				header: Self::Header,
			) -> Result<(), Error>
			where
				Ctx: ReaderContext,
			{
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_update_state(&self) -> proc_macro2::TokenStream {
		let any_client_state = &self.any_data.client_state_ident;
		let any_header = &self.any_data.header_ident;
		let gen_params = &self.generics.params;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = client_state.client_type().to_owned();
					let (client_state, header) = downcast!(
						client_state => #any_client_state::<#gen_params>::#variant_ident,
						header => #any_header::#variant_ident,
					)
					.ok_or_else(|| Error::client_args_type_mismatch(client_type))?;

					let (new_state, new_consensus) =
						client.update_state(ctx, client_id, client_state, header)?;

					Ok((Self::ClientState::#variant_ident(new_state), new_consensus))
				}
			}
		});

		quote! {
			#[doc = "Validates an incoming `header` against the latest consensus state of this client."]
			fn update_state<Ctx>(
				&self,
				ctx: &Ctx,
				client_id: ClientId,
				client_state: Self::ClientState,
				header: Self::Header,
			) -> Result<(Self::ClientState, ConsensusUpdateResult<Ctx>), Error>
			where
				Ctx: ReaderContext,
			{
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_update_state_on_misbehaviour(&self) -> proc_macro2::TokenStream {
		let any_client_state = &self.any_data.client_state_ident;
		let any_header = &self.any_data.header_ident;
		let gen_params = &self.generics.params;
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = client_state.client_type().to_owned();
					let (client_state, header) = downcast!(
						client_state => #any_client_state::<#gen_params>::#variant_ident,
						header => #any_header::#variant_ident,
					)
					.ok_or_else(|| Error::client_args_type_mismatch(client_type))?;

					let client_state = client.update_state_on_misbehaviour(client_state, header)?;
					Ok(Self::ClientState::#variant_ident(client_state))
				}
			}
		});

		quote! {
			fn update_state_on_misbehaviour(
				&self,
				client_state: Self::ClientState,
				header: Self::Header,
			) -> Result<Self::ClientState, Error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_check_for_misbehaviour(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = client_state.client_type().to_owned();
					let (client_state, header) = downcast!(
						client_state => Self::ClientState::#variant_ident,
						header => Self::Header::#variant_ident,
					)
					.ok_or_else(|| Error::client_args_type_mismatch(client_type))?;
					client.check_for_misbehaviour(ctx, client_id, client_state, header)
				}
			}
		});

		quote! {
			#[doc = "Checks for misbehaviour in an incoming header"]
			fn check_for_misbehaviour<Ctx>(
				&self,
				ctx: &Ctx,
				client_id: ClientId,
				client_state: Self::ClientState,
				header: Self::Header,
			) -> Result<bool, Error>
			where
				Ctx: ReaderContext,
			{
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_upgrade_and_update_state(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = client_state.client_type().to_owned();
					let (client_state, consensus_state) = downcast!(
						client_state => Self::ClientState::#variant_ident,
						consensus_state => Self::ConsensusState::#variant_ident,
					)
					.ok_or_else(|| Error::client_args_type_mismatch(client_type))?;

					let (new_state, new_consensus) = client.verify_upgrade_and_update_state::<Ctx>(
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
			fn verify_upgrade_and_update_state<Ctx: ReaderContext>(
				&self,
				client_state: &Self::ClientState,
				consensus_state: &Self::ConsensusState,
				proof_upgrade_client: Vec<u8>,
				proof_upgrade_consensus_state: Vec<u8>,
			) -> Result<(Self::ClientState, ConsensusUpdateResult<Ctx>), Error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_client_consensus_state(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = client_state.client_type().to_owned();
					let client_state = downcast!(
						client_state => Self::ClientState::#variant_ident
					)
					.ok_or_else(|| Error::client_args_type_mismatch(client_type))?;

					client.verify_client_consensus_state(
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
			fn verify_client_consensus_state<Ctx: ReaderContext>(
				&self,
				ctx: &Ctx,
				client_state: &Self::ClientState,
				height: Height,
				prefix: &CommitmentPrefix,
				proof: &CommitmentProofBytes,
				root: &CommitmentRoot,
				client_id: &ClientId,
				consensus_height: Height,
				expected_consensus_state: &Ctx::AnyConsensusState,
			) -> Result<(), Error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_connection_state(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = client_state.client_type().to_owned();
					let client_state = downcast!(client_state => Self::ClientState::#variant_ident)
						.ok_or_else(|| Error::client_args_type_mismatch(client_type))?;

					client.verify_connection_state(
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
			fn verify_connection_state<Ctx: ReaderContext>(
				&self,
				ctx: &Ctx,
				client_id: &ClientId,
				client_state: &Self::ClientState,
				height: Height,
				prefix: &CommitmentPrefix,
				proof: &CommitmentProofBytes,
				root: &CommitmentRoot,
				connection_id: &ConnectionId,
				expected_connection_end: &ConnectionEnd,
			) -> Result<(), Error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_channel_state(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = client_state.client_type().to_owned();
					let client_state = downcast!(client_state => Self::ClientState::#variant_ident)
						.ok_or_else(|| Error::client_args_type_mismatch(client_type))?;

					client.verify_channel_state(
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
			fn verify_channel_state<Ctx: ReaderContext>(
				&self,
				ctx: &Ctx,
				client_id: &ClientId,
				client_state: &Self::ClientState,
				height: Height,
				prefix: &CommitmentPrefix,
				proof: &CommitmentProofBytes,
				root: &CommitmentRoot,
				port_id: &PortId,
				channel_id: &ChannelId,
				expected_channel_end: &ChannelEnd,
			) -> Result<(), Error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_client_full_state(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = client_state.client_type().to_owned();
					let client_state = downcast!(
						client_state => Self::ClientState::#variant_ident
					)
					.ok_or_else(|| Error::client_args_type_mismatch(client_type))?;

					client.verify_client_full_state(
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
			fn verify_client_full_state<Ctx: ReaderContext>(
				&self,
				ctx: &Ctx,
				client_state: &Self::ClientState,
				height: Height,
				prefix: &CommitmentPrefix,
				proof: &CommitmentProofBytes,
				root: &CommitmentRoot,
				client_id: &ClientId,
				client_state_on_counterparty: &Ctx::AnyClientState,
			) -> Result<(), Error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_packet_data(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = client_state.client_type().to_owned();
					let client_state = downcast!(
						client_state => Self::ClientState::#variant_ident
					)
					.ok_or_else(|| Error::client_args_type_mismatch(client_type))?;

					client.verify_packet_data(
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
			fn verify_packet_data<Ctx: ReaderContext>(
				&self,
				ctx: &Ctx,
				client_id: &ClientId,
				client_state: &Self::ClientState,
				height: Height,
				connection_end: &ConnectionEnd,
				proof: &CommitmentProofBytes,
				root: &CommitmentRoot,
				port_id: &PortId,
				channel_id: &ChannelId,
				sequence: Sequence,
				commitment: PacketCommitment,
			) -> Result<(), Error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_packet_acknowledgement(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = client_state.client_type().to_owned();
					let client_state = downcast!(
						client_state => Self::ClientState::#variant_ident
					)
					.ok_or_else(|| Error::client_args_type_mismatch(client_type))?;

					client.verify_packet_acknowledgement(
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
			fn verify_packet_acknowledgement<Ctx: ReaderContext>(
				&self,
				ctx: &Ctx,
				client_id: &ClientId,
				client_state: &Self::ClientState,
				height: Height,
				connection_end: &ConnectionEnd,
				proof: &CommitmentProofBytes,
				root: &CommitmentRoot,
				port_id: &PortId,
				channel_id: &ChannelId,
				sequence: Sequence,
				ack_commitment: AcknowledgementCommitment,
			) -> Result<(), Error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_next_sequence_recv(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = client_state.client_type().to_owned();
					let client_state = downcast!(
						client_state => Self::ClientState::#variant_ident
					)
					.ok_or_else(|| Error::client_args_type_mismatch(client_type))?;

					client.verify_next_sequence_recv(
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
			fn verify_next_sequence_recv<Ctx: ReaderContext>(
				&self,
				ctx: &Ctx,
				client_id: &ClientId,
				client_state: &Self::ClientState,
				height: Height,
				connection_end: &ConnectionEnd,
				proof: &CommitmentProofBytes,
				root: &CommitmentRoot,
				port_id: &PortId,
				channel_id: &ChannelId,
				sequence: Sequence,
			) -> Result<(), Error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	fn impl_fn_verify_packet_receipt_absence(&self) -> proc_macro2::TokenStream {
		let cases = self.clients.iter().map(|client| {
			let variant_ident = &client.variant_ident;
			let attrs = &client.attrs;
			let _client_state_path = &client.client_state_path;
			quote! {
				#(#attrs)*
				Self::#variant_ident(client) => {
					let client_type = client_state.client_type().to_owned();
					let client_state = downcast!(
						client_state => Self::ClientState::#variant_ident
					)
					.ok_or_else(|| Error::client_args_type_mismatch(client_type))?;

					client.verify_packet_receipt_absence(
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
			fn verify_packet_receipt_absence<Ctx: ReaderContext>(
				&self,
				ctx: &Ctx,
				client_id: &ClientId,
				client_state: &Self::ClientState,
				height: Height,
				connection_end: &ConnectionEnd,
				proof: &CommitmentProofBytes,
				root: &CommitmentRoot,
				port_id: &PortId,
				channel_id: &ChannelId,
				sequence: Sequence,
			) -> Result<(), Error> {
				match self {
					#(#cases)*
				}
			}
		}
	}

	pub fn impl_client_def(&self) -> proc_macro2::TokenStream {
		let this = &self.self_ident;
		let any_header = &self.any_data.header_ident;
		let any_client_state = &self.any_data.client_state_ident;
		let any_consensus_state = &self.any_data.consensus_state_ident;
		let gens = &self.generics;
		let gens_where = &self.generics.where_clause;
		let gen_params = &self.generics.params;

		let fn_verify_header = self.impl_fn_verify_header();
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
			impl #gens ClientDef for #this #gens #gens_where {
				type Header = #any_header;
				type ClientState = #any_client_state::<#gen_params>;
				type ConsensusState = #any_consensus_state;

				#fn_verify_header
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
