{
  description = ''
    The ibc-proto-compiler is a simple command-line tool to automate the compilation of
    Protocol Buffers message definitions from the Cosmos SDK and IBC-Go
    to Rust source code with Prost, for use in the ibc-proto crate in the ibc-rs project.
  '';

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    utils.url = "github:numtide/flake-utils";
    rust-overlay.url = "github:oxalica/rust-overlay";
    crate2nix = {
      url = "github:balsoft/crate2nix/tools-nix-version-comparison";
      flake = false;
    };
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, utils, rust-overlay, crate2nix, ... }:
    utils.lib.eachDefaultSystem
      (system:
       let
          name = "ibc-proto-compiler";

          # Imports
          pkgs = import nixpkgs {
            inherit system;
            overlays = [
              rust-overlay.overlay
              (self: super: {
                # Because rust-overlay bundles multiple rust packages into one
                # derivation, specify that mega-bundle here, so that crate2nix
                # will use them automatically.
                rustc = self.rust-bin.stable.latest.default;
                cargo = self.rust-bin.stable.latest.default;
              })
            ];
          };
          inherit (import "${crate2nix}/tools.nix" { inherit pkgs; })
            generatedCargoNix;

          # Create the cargo2nix project
          project = pkgs.callPackage (generatedCargoNix {
            inherit name;
            src = ./.;
          }) {
            # Individual crate overrides go here
            # Example: https://github.com/balsoft/simple-osd-daemons/blob/6f85144934c0c1382c7a4d3a2bbb80106776e270/flake.nix#L28-L50
            defaultCrateOverrides = pkgs.defaultCrateOverrides // {
              # The ibc-proto-compiler crate itself is overriden here. Typically we
              # configure non-Rust dependencies (see below) here.
              ${name} = oldAttrs: {
                nativeBuildInputs = with pkgs; [ rustc cargo pkgconfig ];
              };
              prost-build = oldAttrs: {
                buildInputs = [pkgs.protobuf];
                PROTOC = "${pkgs.protobuf}/bin/protoc";
              };
            };
          };
        in rec {
          packages.${name} = project.rootCrate.build;

          # `nix build`
          defaultPackage = packages.${name};

          # `nix run`
          apps = {
            ${name} = utils.lib.mkApp {
              inherit name;
              drv = packages.${name};
            };
          };
          defaultApp = apps.${name};

          # `nix develop`
          devShell =
          let cosmos-sdk-rev = "7648bfca45b9d0897103ec739210607dce77c4fb";
              ibc-go-rev = "333c1f338b2a14a1928a6f8ab64c37123c0e97b6";
              compileScript = pkgs.writeShellScriptBin "compile" ''
                ${self.packages.${system}.${name}}/bin/${name} clone --out /tmp/cosmos --sdk-commit ${cosmos-sdk-rev} --ibc-go-commit ${ibc-go-rev}
                ${self.packages.${system}.${name}}/bin/${name} compile --sdk /tmp/cosmos/sdk --ibc /tmp/cosmos/ibc --out ../proto/src/prost
                ## rm -rf /tmp/cosmos/
              '';
          in
            pkgs.mkShell {
              packages = [ compileScript ];
              inputsFrom = builtins.attrValues self.packages.${system};
              buildInputs = with pkgs; [ cargo cargo-watch trunk ];
              RUST_SRC_PATH = "${pkgs.rust.packages.stable.rustPlatform.rustLibSrc}";
            };
        }
      );
}
