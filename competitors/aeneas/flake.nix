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

        # End-to-end pipeline: Rust -> Charon -> Aeneas -> Lean model -> proof.
        # The crucial step is [4/5] `cp lean-gen -> lean-proof`: the proof
        # imports `lean-proof/Quicksort.lean`, so without this copy `lake build`
        # silently re-checks the STALE model and a Rust edit looks "proven" when
        # it was never re-translated. This target keeps the model and the proof
        # in lockstep so a `lib.rs` change is actually re-certified end to end.
        pipeline = pkgs.writeShellApplication {
          name = "aeneas-pipeline";
          runtimeInputs = [
            charonPkg                                    # `charon`
            aeneasPkg                                    # `aeneas`
            (fenix.packages.${system}.default.toolchain) # cargo/rustc
            pkgs.elan                                    # `lake` for the proof
            pkgs.coreutils                               # `cp`
          ];
          text = ''
            root="$PWD"
            if [ ! -f "$root/flake.nix" ] || [ ! -d "$root/quicksort" ]; then
              echo "error: run from competitors/aeneas (where flake.nix lives)" >&2
              exit 1
            fi
            # Keep elan's toolchains inside the folder, never the user's HOME
            # (mirrors the devShell's shellHook).
            export ELAN_HOME="$root/lean-proof/.elan"

            echo "[1/5] cargo build + test"
            ( cd "$root/quicksort" && cargo build && cargo test )

            echo "[2/5] charon cargo --preset=aeneas -> quicksort.llbc"
            ( cd "$root/quicksort" && charon cargo --preset=aeneas )

            echo "[3/5] aeneas -backend lean -> lean-gen/Quicksort.lean"
            ( cd "$root/quicksort" && aeneas -backend lean quicksort.llbc -dest "$root/lean-gen" )

            echo "[4/5] sync generated model into the proof project"
            cp "$root/lean-gen/Quicksort.lean" "$root/lean-proof/Quicksort.lean"

            echo "[5/5] lake build (typecheck the model AND the proof)"
            ( cd "$root/lean-proof" && lake build )

            echo ""
            echo "OK: proof re-checked against the freshly generated model."
          '';
        };
        pipelineApp = {
          type = "app";
          program = "${pipeline}/bin/aeneas-pipeline";
        };
      in {
        packages.pipeline = pipeline;
        apps.default = pipelineApp;
        apps.pipeline = pipelineApp;

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
          '';
        };
      });
}
