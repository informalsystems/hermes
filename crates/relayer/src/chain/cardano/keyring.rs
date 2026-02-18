//! Cardano keyring implementation with CIP-1852 derivation

use super::error::Error;
use blake2::digest::{Update, VariableOutput};
use blake2::Blake2bVar;
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use slip10::BIP32Path;
use std::str::FromStr;

/// Cardano keyring for signing transactions
#[derive(Clone, Debug)]
pub struct CardanoKeyring {
    signing_key: SigningKey,
    verifying_key: VerifyingKey,
}

impl CardanoKeyring {
    /// Create a keyring from a bech32-encoded private key (ed25519_sk...)
    pub fn from_bech32_key(bech32_key: &str) -> Result<Self, Error> {
        use bech32::FromBase32;

        // Decode bech32 key
        let (hrp, data, _variant) = bech32::decode(bech32_key)
            .map_err(|e| Error::Keyring(format!("Invalid bech32 key: {:?}", e)))?;

        if hrp != "ed25519_sk" {
            return Err(Error::Keyring(format!(
                "Expected ed25519_sk prefix, got: {}",
                hrp
            )));
        }

        // Convert from base32 (u5) to bytes
        let bytes = Vec::<u8>::from_base32(&data)
            .map_err(|e| Error::Keyring(format!("Failed to decode base32: {:?}", e)))?;

        // Data should be 32 bytes for Ed25519 private key
        if bytes.len() != 32 {
            return Err(Error::Keyring(format!(
                "Invalid key length: expected 32, got {}",
                bytes.len()
            )));
        }

        let mut key_bytes = [0u8; 32];
        key_bytes.copy_from_slice(&bytes);

        let signing_key = SigningKey::from_bytes(&key_bytes);
        let verifying_key = signing_key.verifying_key();

        Ok(Self {
            signing_key,
            verifying_key,
        })
    }

    /// Create a new keyring from a mnemonic phrase
    /// Uses CIP-1852 derivation: m/1852'/1815'/account'/2'/0'
    pub fn from_mnemonic(mnemonic: &str, account: u32) -> Result<Self, Error> {
        // Parse mnemonic using tiny-bip39 crate (hyphenated crate name, underscore in code)
        let mnemonic = bip39::Mnemonic::from_phrase(mnemonic, bip39::Language::English)
            .map_err(|e| Error::Keyring(format!("Invalid mnemonic: {:?}", e)))?;

        // Generate seed
        let seed = bip39::Seed::new(&mnemonic, "");
        let seed_bytes = seed.as_bytes();

        // CIP-1852 path: m/1852'/1815'/account'/2'/0'
        // 1852' = purpose (CIP-1852), 1815' = coin type (Cardano), 2' = payment key role
        let path = BIP32Path::from_str(&format!("m/1852'/1815'/{}'/2'/0'", account))
            .map_err(|e| Error::Keyring(format!("Invalid derivation path: {:?}", e)))?;

        // Derive key using SLIP-0010 Ed25519
        let derived_key = slip10::derive_key_from_path(seed_bytes, slip10::Curve::Ed25519, &path)
            .map_err(|e| Error::Keyring(format!("Key derivation failed: {:?}", e)))?;

        // Create Ed25519 signing key
        let signing_key = SigningKey::from_bytes(&derived_key.key);
        let verifying_key = signing_key.verifying_key();

        Ok(Self {
            signing_key,
            verifying_key,
        })
    }

    /// Get the public key (verifying key)
    pub fn verifying_key(&self) -> &VerifyingKey {
        &self.verifying_key
    }

    /// Sign a message
    pub fn sign(&self, message: &[u8]) -> Signature {
        self.signing_key.sign(message)
    }

    /// Get the Cardano payment address (enterprise address for simplicity)
    /// Enterprise address = (0x60 | network_id) | Blake2b-224(verifying_key)
    pub fn address(&self, network_id: u8) -> String {
        let vkey_bytes = self.verifying_key.as_bytes();

        // Hash the public key with Blake2b-224 (28 bytes)
        let mut hasher = Blake2bVar::new(28).expect("Blake2b-224 initialization must succeed");
        hasher.update(vkey_bytes);
        let mut payment_hash = [0u8; 28];
        hasher
            .finalize_variable(&mut payment_hash)
            .expect("Blake2b-224 finalize must succeed");

        // Construct enterprise address: header | payment_hash
        //
        // Address header encoding:
        // - High nibble = address type (enterprise keyhash = 0b0110 = 6)
        // - Low nibble  = network id (testnet = 0, mainnet = 1)
        let header = 0x60 | (network_id & 0x0f);

        let mut address_bytes = vec![header];
        address_bytes.extend_from_slice(&payment_hash);

        // Encode as hex
        hex::encode(address_bytes)
    }

    /// Create a test keyring with deterministic keys
    pub fn new_for_testing() -> Result<Self, Error> {
        // Standard test mnemonic (DO NOT USE IN PRODUCTION)
        let mnemonic = "test walk nut penalty hip pave soap entry language right filter choice";
        Self::from_mnemonic(mnemonic, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_keyring_derivation() {
        let mnemonic = "test walk nut penalty hip pave soap entry language right filter choice";
        let keyring = CardanoKeyring::from_mnemonic(mnemonic, 0).unwrap();

        // Should generate consistent keys
        let address = keyring.address(0);
        assert!(!address.is_empty());
        assert!(address.starts_with("60")); // Enterprise testnet address
    }

    #[test]
    fn test_signing() {
        let keyring = CardanoKeyring::new_for_testing().unwrap();
        let message = b"test message";

        let signature = keyring.sign(message);

        // Verify the signature
        use ed25519_dalek::Verifier;
        assert!(keyring.verifying_key.verify(message, &signature).is_ok());
    }

    #[test]
    fn test_different_accounts() {
        let mnemonic = "test walk nut penalty hip pave soap entry language right filter choice";
        let keyring1 = CardanoKeyring::from_mnemonic(mnemonic, 0).unwrap();
        let keyring2 = CardanoKeyring::from_mnemonic(mnemonic, 1).unwrap();

        // Different accounts should produce different addresses
        assert_ne!(keyring1.address(0), keyring2.address(0));
    }

    #[test]
    fn test_from_bech32_key() {
        let key = "ed25519_sk1rvgjxs8sddhl46uqtv862s53vu4jf6lnk63rcn7f0qwzyq85wnlqgrsx42";
        let result = CardanoKeyring::from_bech32_key(key);
        assert!(
            result.is_ok(),
            "Failed to load from bech32 key: {:?}",
            result.err()
        );
    }
}
