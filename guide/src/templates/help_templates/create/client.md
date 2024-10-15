DESCRIPTION:
Create a new IBC client

USAGE:
    hermes create client [OPTIONS] --host-chain <HOST_CHAIN_ID> --reference-chain <REFERENCE_CHAIN_ID>

OPTIONS:
        --clock-drift <CLOCK_DRIFT>
            The maximum allowed clock drift for this client.
            
            The clock drift is a correction parameter. It helps deal with clocks that are only
            approximately synchronized between the source and destination chains of this client. The
            destination chain for this client uses the clock drift parameter when deciding to accept
            or reject a new header (originating from the source chain) for this client. If this
            option is not specified, a suitable clock drift value is derived from the chain
            configurations.

    -h, --help
            Print help information

        --trust-threshold <TRUST_THRESHOLD>
            Override the trust threshold specified in the configuration.
            
            The trust threshold defines what fraction of the total voting power of a known and
            trusted validator set is sufficient for a commit to be accepted going forward.

        --trusting-period <TRUSTING_PERIOD>
            Override the trusting period specified in the config.
            
            The trusting period specifies how long a validator set is trusted for (must be shorter
            than the chain's unbonding period).

        --wasm-checksum <WASM_CHECKSUM>
            The hex-encoded SHA256 checksum of the WASM contract that backs this client. If
            specified, the client will be created as an ICS 08 Wasm client. Otherwise, the client
            will be created as an ICS 07 Tendermint client. Only Wasm clients wrapping an ICS 07
            Tendermint client are supported

REQUIRED:
        --host-chain <HOST_CHAIN_ID>
            Identifier of the chain that hosts the client

        --reference-chain <REFERENCE_CHAIN_ID>
            Identifier of the chain targeted by the client
