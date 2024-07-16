{
  description = "Nix development dependencies for ibc-rs";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay.url = "github:oxalica/rust-overlay";
    cosmos-nix.url = "github:informalsystems/cosmos.nix";
    cosmos-nix-wasm.url = "github:informalsystems/cosmos.nix/jonathan/ibc-go-wasm";
  };

  outputs = inputs:
    let
    utils = inputs.flake-utils.lib;
  in
    utils.eachSystem
    [
      "aarch64-linux"
      "aarch64-darwin"
      "x86_64-darwin"
      "x86_64-linux"
    ]
      (system:
        let
      nixpkgs = import inputs.nixpkgs {
        inherit system;
            overlays = [
              inputs.rust-overlay.overlays.default
            ];
      };

      cosmos-nix = inputs.cosmos-nix.packages.${system};
          cosmos-nix-wasm = inputs.cosmos-nix-wasm.packages.${system};

          ibc-client-tendermint-cw =
            import ./nix/ibc-client-tendermint-cw.nix
              {
                inherit nixpkgs;
              };
        in
        {
      packages = {
        inherit
          (cosmos-nix)
          apalache
          celestia
          cometbft
          evmos
          gaia6-ordered
          gaia17
          ibc-go-v2-simapp
          ibc-go-v3-simapp
          ibc-go-v4-simapp
          ibc-go-v5-simapp
          ibc-go-v6-simapp
          ibc-go-v7-simapp
          ibc-go-v8-simapp
          interchain-security
          migaloo
          neutron
          juno
          osmosis
          provenance
          stride
          stride-no-admin
          wasmd
          injective
          ;

            inherit
              (cosmos-nix-wasm)
              ibc-go-v7-wasm-simapp
              ;

            ibc-client-tendermint-cw = ibc-client-tendermint-cw;

        python = nixpkgs.python3.withPackages (p: [
          p.toml
        ]);
      };
    });
}
