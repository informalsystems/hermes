//! Cardano transaction signing using Pallas

use super::error::Error;
use super::keyring::CardanoKeyring;
use blake2::Digest;
use pallas_codec::minicbor;
use pallas_primitives::conway::{MintedTx, VKeyWitness};

/// Sign a Cardano transaction
pub fn sign_transaction(
    unsigned_tx_cbor: &[u8],
    keyring: &CardanoKeyring,
) -> Result<Vec<u8>, Error> {
    // 1. Parse the unsigned transaction
    let tx: MintedTx<'_> = minicbor::decode(unsigned_tx_cbor)
        .map_err(|e| Error::CborDecode(format!("Failed to decode transaction: {:?}", e)))?;

    // 2. Extract and hash the transaction body
    // Use the original raw bytes preserved by KeepRaw, not re-encoded bytes
    let tx_body_cbor = tx.transaction_body.raw_cbor();

    // Cardano uses Blake2b-256 for transaction hashing
    use blake2::digest::consts::U32;
    use blake2::Blake2b;
    let mut hasher = Blake2b::<U32>::new();
    hasher.update(tx_body_cbor);
    let tx_hash = hasher.finalize();

    // 3. Sign the transaction hash
    let signature = keyring.sign(tx_hash.as_slice());

    // 4. Create VKeyWitness
    let vkey = keyring.verifying_key().as_bytes().to_vec();
    let sig = signature.to_bytes().to_vec();

    let vkey_witness = VKeyWitness {
        vkey: vkey.into(),
        signature: sig.into(),
    };

    // 5. Reconstruct the transaction with the new witness
    // We need to work around Pallas's KeepRaw immutability by manually building CBOR

    // Get existing witnesses
    let mut new_vkeywitnesses: Vec<VKeyWitness> = tx
        .transaction_witness_set
        .vkeywitness
        .clone()
        .map(|set| set.to_vec())
        .unwrap_or_default();
    new_vkeywitnesses.push(vkey_witness);

    // Encode the new witness set manually
    let mut witness_set_cbor = Vec::new();
    {
        let mut encoder = minicbor::Encoder::new(&mut witness_set_cbor);

        // Count how many witness set fields we have
        let ws = &tx.transaction_witness_set;
        let mut map_size = 1u64; // Always have vkeywitness
        if ws.native_script.is_some() {
            map_size += 1;
        }
        if ws.bootstrap_witness.is_some() {
            map_size += 1;
        }
        if ws.plutus_v1_script.is_some() {
            map_size += 1;
        }
        if ws.plutus_data.is_some() {
            map_size += 1;
        }
        if ws.redeemer.is_some() {
            map_size += 1;
        }
        if ws.plutus_v2_script.is_some() {
            map_size += 1;
        }
        if ws.plutus_v3_script.is_some() {
            map_size += 1;
        }

        // Witness set is a CBOR map
        encoder
            .map(map_size)
            .map_err(|e| Error::Signer(format!("Failed to encode witness map: {:?}", e)))?;

        // Key 0: vkeywitness array
        encoder
            .u8(0)
            .map_err(|e| Error::Signer(format!("Failed to encode key: {:?}", e)))?;
        encoder
            .array(new_vkeywitnesses.len() as u64)
            .map_err(|e| Error::Signer(format!("Failed to encode array: {:?}", e)))?;
        for witness in &new_vkeywitnesses {
            encoder
                .encode(witness)
                .map_err(|e| Error::Signer(format!("Failed to encode witness: {:?}", e)))?;
        }

        // Copy other witness set fields if present
        if let Some(ref native_scripts) = ws.native_script {
            encoder
                .u8(1)
                .map_err(|e| Error::Signer(format!("Failed to encode key: {:?}", e)))?;
            encoder
                .encode(native_scripts)
                .map_err(|e| Error::Signer(format!("Failed to encode native scripts: {:?}", e)))?;
        }

        if let Some(ref bootstrap) = ws.bootstrap_witness {
            encoder
                .u8(2)
                .map_err(|e| Error::Signer(format!("Failed to encode key: {:?}", e)))?;
            encoder
                .encode(bootstrap)
                .map_err(|e| Error::Signer(format!("Failed to encode bootstrap: {:?}", e)))?;
        }

        if let Some(ref plutus_v1) = ws.plutus_v1_script {
            encoder
                .u8(3)
                .map_err(|e| Error::Signer(format!("Failed to encode key: {:?}", e)))?;
            encoder
                .encode(plutus_v1)
                .map_err(|e| Error::Signer(format!("Failed to encode plutus v1: {:?}", e)))?;
        }

        if let Some(ref plutus_data) = ws.plutus_data {
            encoder
                .u8(4)
                .map_err(|e| Error::Signer(format!("Failed to encode key: {:?}", e)))?;
            encoder
                .encode(plutus_data)
                .map_err(|e| Error::Signer(format!("Failed to encode plutus data: {:?}", e)))?;
        }

        if let Some(ref redeemers) = ws.redeemer {
            encoder
                .u8(5)
                .map_err(|e| Error::Signer(format!("Failed to encode key: {:?}", e)))?;
            encoder
                .encode(redeemers)
                .map_err(|e| Error::Signer(format!("Failed to encode redeemers: {:?}", e)))?;
        }

        if let Some(ref plutus_v2) = ws.plutus_v2_script {
            encoder
                .u8(6)
                .map_err(|e| Error::Signer(format!("Failed to encode key: {:?}", e)))?;
            encoder
                .encode(plutus_v2)
                .map_err(|e| Error::Signer(format!("Failed to encode plutus v2: {:?}", e)))?;
        }

        if let Some(ref plutus_v3) = ws.plutus_v3_script {
            encoder
                .u8(7)
                .map_err(|e| Error::Signer(format!("Failed to encode key: {:?}", e)))?;
            encoder
                .encode(plutus_v3)
                .map_err(|e| Error::Signer(format!("Failed to encode plutus v3: {:?}", e)))?;
        }
    }

    // Build the final signed transaction CBOR
    // Conway transaction is an array: [transaction_body, transaction_witness_set, is_valid, auxiliary_data]
    // where auxiliary_data can be null
    let mut signed_tx_cbor = Vec::new();
    {
        let mut encoder = minicbor::Encoder::new(&mut signed_tx_cbor);

        // Conway transactions always have 4 elements
        encoder
            .array(4)
            .map_err(|e| Error::Signer(format!("Failed to encode tx array: {:?}", e)))?;

        // Encode transaction body
        encoder
            .encode(&tx.transaction_body)
            .map_err(|e| Error::Signer(format!("Failed to encode tx body: {:?}", e)))?;

        // Write the witness set CBOR directly (not as a byte string wrapper)
        use std::io::Write;
        encoder
            .writer_mut()
            .write_all(&witness_set_cbor)
            .map_err(|e| Error::Signer(format!("Failed to write witness set: {:?}", e)))?;

        // Encode isValid flag
        encoder
            .bool(tx.success)
            .map_err(|e| Error::Signer(format!("Failed to encode success: {:?}", e)))?;

        // Encode auxiliary data (using Nullable encoding)
        encoder
            .encode(&tx.auxiliary_data)
            .map_err(|e| Error::Signer(format!("Failed to encode aux data: {:?}", e)))?;
    }

    Ok(signed_tx_cbor)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sign_transaction_adds_vkey_witness_and_signature_verifies() {
        fn unsigned_tx_fixture(existing_vkey_witnesses: usize) -> Vec<u8> {
            let mut out = Vec::new();
            let mut enc = minicbor::Encoder::new(&mut out);

            // Conway transaction: [transaction_body, transaction_witness_set, is_valid, auxiliary_data]
            enc.array(4).unwrap();

            // transaction_body is a CBOR map with numeric keys. We include only the minimum set of
            // fields required for decoding: inputs (0), outputs (1), fee (2).
            enc.map(3).unwrap();

            // inputs: Set<TransactionInput> (we omit the optional tag and encode as a plain array)
            enc.u8(0).unwrap();
            enc.array(1).unwrap();
            enc.array(2).unwrap();
            enc.bytes(&[0u8; 32]).unwrap(); // transaction_id hash bytes
            enc.u64(0).unwrap(); // output index

            // outputs: Vec<TransactionOutput> (we use the legacy/array form)
            enc.u8(1).unwrap();
            enc.array(1).unwrap();
            enc.array(3).unwrap();
            enc.bytes(&[1u8; 32]).unwrap(); // address bytes (opaque for this test)
            enc.u64(1).unwrap(); // amount (Value::Coin)
            enc.null().unwrap(); // datum_hash = None

            // fee
            enc.u8(2).unwrap();
            enc.u64(0).unwrap();

            // transaction_witness_set: CBOR map with numeric keys. Start with either empty map or one
            // containing dummy vkey witnesses.
            if existing_vkey_witnesses == 0 {
                enc.map(0).unwrap();
            } else {
                enc.map(1).unwrap();
                enc.u8(0).unwrap();
                enc.array(existing_vkey_witnesses as u64).unwrap();
                for _ in 0..existing_vkey_witnesses {
                    enc.array(2).unwrap();
                    enc.bytes(&[2u8; 32]).unwrap();
                    enc.bytes(&[3u8; 64]).unwrap();
                }
            }

            // is_valid
            enc.bool(true).unwrap();

            // auxiliary_data = null
            enc.null().unwrap();

            out
        }

        let keyring = CardanoKeyring::new_for_testing().unwrap();

        let unsigned = unsigned_tx_fixture(0);
        let unsigned_tx: MintedTx<'_> = minicbor::decode(&unsigned).unwrap();

        let signed = sign_transaction(&unsigned, &keyring).unwrap();
        let signed_tx: MintedTx<'_> = minicbor::decode(&signed).unwrap();

        // Signing must not mutate the transaction body bytes (the hash is over the body).
        assert_eq!(
            signed_tx.transaction_body.raw_cbor(),
            unsigned_tx.transaction_body.raw_cbor()
        );

        // The signing must preserve the success flag and auxiliary data field.
        assert_eq!(signed_tx.success, unsigned_tx.success);
        assert!(matches!(
            signed_tx.auxiliary_data,
            pallas_codec::utils::Nullable::Null
        ));

        // Verify that a vkey witness was added and that it verifies against the tx hash.
        let witnesses = signed_tx
            .transaction_witness_set
            .vkeywitness
            .clone()
            .expect("expected vkey witness set")
            .to_vec();

        let added_witness = witnesses
            .iter()
            .find(|w| w.vkey.as_slice() == keyring.verifying_key().as_bytes())
            .expect("expected witness with the keyring verifying key");

        assert_eq!(added_witness.signature.len(), 64);

        let tx_body_cbor = signed_tx.transaction_body.raw_cbor();

        use blake2::digest::consts::U32;
        use blake2::Blake2b;
        let mut hasher = Blake2b::<U32>::new();
        hasher.update(tx_body_cbor);
        let tx_hash = hasher.finalize();

        use ed25519_dalek::Verifier;
        let signature = {
            let mut sig_bytes = [0u8; 64];
            sig_bytes.copy_from_slice(&added_witness.signature);
            ed25519_dalek::Signature::from_bytes(&sig_bytes)
        };

        keyring
            .verifying_key()
            .verify(tx_hash.as_slice(), &signature)
            .unwrap();
    }

    #[test]
    fn sign_transaction_appends_to_existing_witnesses() {
        fn unsigned_tx_fixture(existing_vkey_witnesses: usize) -> Vec<u8> {
            let mut out = Vec::new();
            let mut enc = minicbor::Encoder::new(&mut out);

            enc.array(4).unwrap();
            enc.map(3).unwrap();

            enc.u8(0).unwrap();
            enc.array(1).unwrap();
            enc.array(2).unwrap();
            enc.bytes(&[0u8; 32]).unwrap();
            enc.u64(0).unwrap();

            enc.u8(1).unwrap();
            enc.array(1).unwrap();
            enc.array(3).unwrap();
            enc.bytes(&[1u8; 32]).unwrap();
            enc.u64(1).unwrap();
            enc.null().unwrap();

            enc.u8(2).unwrap();
            enc.u64(0).unwrap();

            enc.map(1).unwrap();
            enc.u8(0).unwrap();
            enc.array(existing_vkey_witnesses as u64).unwrap();
            for _ in 0..existing_vkey_witnesses {
                enc.array(2).unwrap();
                enc.bytes(&[2u8; 32]).unwrap();
                enc.bytes(&[3u8; 64]).unwrap();
            }

            enc.bool(true).unwrap();
            enc.null().unwrap();

            out
        }

        let keyring = CardanoKeyring::new_for_testing().unwrap();

        let unsigned = unsigned_tx_fixture(1);
        let signed = sign_transaction(&unsigned, &keyring).unwrap();
        let signed_tx: MintedTx<'_> = minicbor::decode(&signed).unwrap();

        let witnesses = signed_tx
            .transaction_witness_set
            .vkeywitness
            .clone()
            .expect("expected vkey witness set")
            .to_vec();

        assert_eq!(witnesses.len(), 2);
    }

    #[test]
    fn sign_transaction_rejects_invalid_cbor() {
        let keyring = CardanoKeyring::new_for_testing().unwrap();

        let err = sign_transaction(&[0xff], &keyring).unwrap_err();
        assert!(matches!(err, Error::CborDecode(_)));
    }
}
