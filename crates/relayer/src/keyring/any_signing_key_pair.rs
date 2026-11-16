use serde::{ser::SerializeStruct, Serialize, Serializer};

use super::{
    CosmosAccountKeyType, CosmosKeyPair, CosmosSigner, Ed25519KeyPair, KeyType, NamadaKeyPair,
    Secp256k1KeyPair, SigningKeyPair,
};

#[derive(Clone, Debug, Serialize)]
#[serde(untagged)]
pub enum AnySigningKeyPair {
    Secp256k1(Secp256k1KeyPair),
    Cosmos(#[serde(serialize_with = "serialize_cosmos_key")] CosmosKeyPair),
    Ed25519(Ed25519KeyPair),
    Namada(NamadaKeyPair),
}

impl AnySigningKeyPair {
    pub fn account(&self) -> String {
        match self {
            Self::Secp256k1(key_pair) => key_pair.account(),
            Self::Cosmos(key_pair) => key_pair.signer_address(),
            Self::Ed25519(key_pair) => key_pair.account(),
            Self::Namada(key_pair) => key_pair.account(),
        }
    }

    pub fn key_type(&self) -> KeyType {
        match self {
            Self::Secp256k1(_) => Secp256k1KeyPair::KEY_TYPE,
            Self::Cosmos(key_pair) => match key_pair.key_type() {
                CosmosAccountKeyType::Secp256k1 => KeyType::Secp256k1,
                CosmosAccountKeyType::MlDsa65 => KeyType::MlDsa65,
            },
            Self::Ed25519(_) => Ed25519KeyPair::KEY_TYPE,
            Self::Namada(_) => NamadaKeyPair::KEY_TYPE,
        }
    }

    pub fn downcast<T: Clone + 'static>(&self) -> Option<T> {
        match self {
            Self::Secp256k1(key_pair) => {
                // Older callers pass a concrete secp256k1 key to Cosmos chains.
                return key_pair.as_any().downcast_ref::<T>().cloned().or_else(|| {
                    let wrapped = CosmosKeyPair::Secp256k1(key_pair.clone());
                    let wrapped: &dyn core::any::Any = &wrapped;
                    wrapped.downcast_ref::<T>().cloned()
                });
            }
            Self::Cosmos(key_pair) => {
                let dynamic_key: &dyn core::any::Any = key_pair;
                return dynamic_key
                    .downcast_ref::<T>()
                    .cloned()
                    .or_else(|| match key_pair {
                        CosmosKeyPair::Secp256k1(key) => key.as_any().downcast_ref::<T>().cloned(),
                        CosmosKeyPair::MlDsa65(_) => None,
                    });
            }
            Self::Ed25519(key_pair) => key_pair.as_any(),
            Self::Namada(key_pair) => key_pair.as_any(),
        }
        .downcast_ref::<T>()
        .cloned()
    }
}

impl From<Secp256k1KeyPair> for AnySigningKeyPair {
    fn from(key_pair: Secp256k1KeyPair) -> Self {
        Self::Secp256k1(key_pair)
    }
}

impl From<Ed25519KeyPair> for AnySigningKeyPair {
    fn from(key_pair: Ed25519KeyPair) -> Self {
        Self::Ed25519(key_pair)
    }
}

impl From<NamadaKeyPair> for AnySigningKeyPair {
    fn from(key_pair: NamadaKeyPair) -> Self {
        Self::Namada(key_pair)
    }
}

impl From<CosmosKeyPair> for AnySigningKeyPair {
    fn from(key_pair: CosmosKeyPair) -> Self {
        Self::Cosmos(key_pair)
    }
}

fn serialize_cosmos_key<S: Serializer>(
    key: &CosmosKeyPair,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    match key {
        CosmosKeyPair::Secp256k1(key) => key.serialize(serializer),
        CosmosKeyPair::MlDsa65(_) => {
            let mut public = serializer.serialize_struct("MlDsa65Account", 2)?;
            public.serialize_field("account", &key.signer_address())?;
            public.serialize_field("key_type", &key.key_type())?;
            public.end()
        }
    }
}
