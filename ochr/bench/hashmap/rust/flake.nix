{
  description = "Agent-effort benchmark, hashmap, condition rust: unverified Rust (the floor)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ rust-overlay.overlays.default ];
        };
        # A stable toolchain. The "default" profile carries rust-docs: the Rust
        # Book, the standard library API and the Reference as offline HTML,
        # which make-sandbox.sh links into the sandbox as docs/rust.
        rust = pkgs.rust-bin.stable."1.95.0".default;
      in {
        packages.rust = rust;
        packages.docs = pkgs.runCommand "rust-docs-html" { } ''
          ln -s ${rust}/share/doc/rust/html $out
        '';
        devShells.default = pkgs.mkShell {
          # python3 runs ../../common/check_fixed.py from grade.sh.
          packages = [ rust pkgs.python3 ];
        };
      });
}
