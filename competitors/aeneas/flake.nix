{
  description = "Aeneas competitor: in-place quicksort, Rust -> Charon -> Aeneas -> Lean (proven)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    # Charon: Rust (MIR/HIR) -> LLBC. Pins the exact rustc nightly it needs.
    charon.url = "github:AeneasVerif/charon";

    # Aeneas: LLBC -> pure functional model + Lean extraction.
    # Make Aeneas follow the *same* Charon so the LLBC format versions match
    # (Aeneas refuses LLBC produced by a mismatched Charon). The pinned aeneas
    # revision is the one `lean-proof/lakefile.lean` `require`s as a git dep, so
    # the proof typechecks against exactly the runtime library shipped here.
    aeneas = {
      url = "github:AeneasVerif/aeneas";
      inputs.charon.follows = "charon";
    };

    # Rust nightly for the quicksort crate itself (so `cargo build` works in the
    # shell independently of Charon's internal toolchain).
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, charon, aeneas, fenix }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        charonPkg = charon.packages.${system}.default;
        aeneasPkg = aeneas.packages.${system}.default;
      in {
        devShells.default = pkgs.mkShell {
          packages = [
            charonPkg                                    # `charon`
            aeneasPkg                                    # `aeneas`
            (fenix.packages.${system}.default.toolchain) # cargo/rustc for the crate
            # `elan` manages the Lean toolchain for the PROOF project. The proof
            # imports the real `Aeneas` Lean library (Lean v4.30.0-rc2 + Mathlib),
            # which is NOT in nixpkgs, so we let elan fetch the pinned toolchain
            # named in `lean-proof/lean-toolchain` and lake fetch Mathlib oleans
            # via `lake exe cache get`. (This is the isolated sandbox toolchain;
            # it does not touch the repo-root Lean 4.16 used by the Och project.)
            pkgs.elan
          ];
          # Keep elan's toolchains inside the folder, never the user's HOME.
          shellHook = ''
            export ELAN_HOME="$PWD/lean-proof/.elan"
            echo "Aeneas competitor shell: charon, aeneas, cargo, elan on PATH."
            echo ""
            echo "Translate:  cd quicksort && charon cargo --preset=aeneas \\"
            echo "            && aeneas -backend lean quicksort.llbc -dest ../lean-gen"
            echo "Prove:      cd lean-proof && lake update && lake build"
            echo "            (lake update fetches Mathlib oleans via cache; minutes, not hours)"
          '';
        };
      });
}
