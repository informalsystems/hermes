- Add a pluggable `ExtensionSigner` (`TxConfig::extension_signer`) that adds
  extension options, such as an additional post-quantum signature, to every
  transaction after its `AuthInfo` is final and before the classical signature,
  for chains that require a second signature
  ([\#4435](https://github.com/informalsystems/hermes/pull/4435))
