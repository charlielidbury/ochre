{
  description = "Agent-effort benchmark, hashmap, condition lean: pure functional Lean 4 + Mathlib";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    # Offline Lean documentation for the sandbox (make-sandbox.sh links these
    # into docs/). They are the sources of the books, in Verso, readable as text.
    tpil = { url = "github:leanprover/theorem_proving_in_lean4"; flake = false; };
    fpil = { url = "github:leanprover/fp-lean"; flake = false; };
    reference-manual = { url = "github:leanprover/reference-manual"; flake = false; };
  };

  outputs = { self, nixpkgs, flake-utils, tpil, fpil, reference-manual }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        # The Lean toolchain itself is the one named in lean-toolchain
        # (leanprover/lean4:v4.31.0), dispatched by elan; Mathlib is pinned in
        # lakefile.toml / lake-manifest.json and its oleans come from
        # `lake exe cache get`.
        packages.docs = pkgs.runCommand "lean-docs" { } ''
          mkdir -p $out
          ln -s ${tpil} $out/theorem-proving-in-lean4
          ln -s ${fpil} $out/functional-programming-in-lean
          ln -s ${reference-manual} $out/lean-reference-manual
        '';
        devShells.default = pkgs.mkShell {
          # python3 runs the grader's scripts from grade.sh.
          packages = [ pkgs.elan pkgs.python3 ];
        };
      });
}
