{
  description = "Nix development dependencies for ibc-rs";

  inputs = {
    nixpkgs.url = github:nixos/nixpkgs/nixpkgs-unstable;
    flake-utils.url = github:numtide/flake-utils;
    cosmos-nix.url = github:informalsystems/cosmos.nix;
  };

  outputs = inputs: let
    utils = inputs.flake-utils.lib;
  in
    utils.eachSystem
    [
      "aarch64-linux"
      "aarch64-darwin"
      "x86_64-darwin"
      "x86_64-linux"
    ]
    (system: let
      nixpkgs = import inputs.nixpkgs {
        inherit system;
      };

      cosmos-nix = inputs.cosmos-nix.packages.${system};
    in {
      packages = {
        inherit
          (cosmos-nix)
          apalache
          celestia
          cometbft
          evmos
          gaia6-ordered
          gaia13
          gaia14
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
          stride-consumer-no-admin
          stride-consumer
          wasmd
          injective
          ;

        python = nixpkgs.python3.withPackages (p: [
          p.toml
        ]);
      };
    });
}
