{
  description = "Ochre — a programming language, and its core calculus Och";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    lean4-nix = {
      url = "github:lenianiva/lean4-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, lean4-nix, fenix }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ (lean4-nix.readToolchainFile ./lean/lean-toolchain) ];
        };

        # compiler-macros uses #![feature(...)], so we need nightly.
        rustNightly = fenix.packages.${system}.minimal.toolchain;
        rustPlatform = pkgs.makeRustPlatform {
          cargo = rustNightly;
          rustc = rustNightly;
        };

        # Rust compiler (compiler/ workspace, includes compiler-macros)
        compiler = rustPlatform.buildRustPackage {
          pname = "ochre-compiler";
          version = "0.1.0";
          src = pkgs.lib.cleanSource ./compiler;
          cargoLock.lockFile = ./compiler/Cargo.lock;
        };

        # Lean formalisation of the Och core calculus (lean/)
        och = pkgs.lean.buildLeanPackage {
          name = "Och";
          src = pkgs.lib.cleanSource ./lean;
          roots = [ "Och" ];
        };

      in {
        packages = {
          inherit compiler;
          och-lean = och.modRoot;
          default = compiler;
        };

        checks = {
          inherit compiler;
          och-lean = och.modRoot;
        };

        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            # Rust (nightly, matching the build)
            (fenix.packages.${system}.default.toolchain)
            # Lean (pinned via lean4-nix to lean/lean-toolchain)
            lean.lean-all
            # Agda playground
            (agda.withPackages (p: [ p.standard-library ]))
            # OCaml scaffolding
            ocaml dune_3
            # Typesetting
            typst pandoc
          ];
        };
      });
}
