{
  description = "Verus in-place quicksort competitor (SMT-backed verification of native Rust), built from source";

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

        # ------------------------------------------------------------------
        # Verus, built FROM SOURCE (no platform-specific prebuilt zip).
        #
        # We pin the exact `release/<version>` git tag so the toolchain that
        # checks `quicksort.rs` is the same version a release would ship, but
        # we build it ourselves with `fetchFromGitHub` + Verus's `vargo` build
        # system. Because the input is *source* (content-addressed, not an
        # x86-linux binary), this derivation is portable across systems — it
        # builds on any platform rust-overlay + nixpkgs support, rather than
        # being nailed to `x86_64-linux` by a prebuilt release archive.
        #
        # The version string Verus uses (`0.YYYY.MM.DD.<shortsha>`) embeds the
        # commit, so `verusVersion` and `verusRev` stay in lock-step: the short
        # sha at the end of `verusVersion` is the prefix of `verusRev`.
        # ------------------------------------------------------------------
        verusVersion = "0.2026.05.31.5dd6d83";
        verusRev = "5dd6d836101ac38ed3ebcfdff61a0e98e0c586fe";
        verusToolchain = "1.95.0"; # from upstream rust-toolchain.toml
        z3Version = "4.12.5"; # the z3 version Verus pins (source/tools/get-z3.sh)

        verusSrc = pkgs.fetchFromGitHub {
          owner = "verus-lang";
          repo = "verus";
          rev = verusRev;
          hash = "sha256-c+ffbI183ZKjB6JJccrmD7daJSJR9aT0jV1i88qin2E=";
        };

        # The exact stable toolchain Verus is pinned to, WITH the rustc-dev /
        # rust-src / llvm-tools components vargo needs to build `rust_verify`
        # (which is a rustc driver linking against librustc_driver).
        rustToolchain = pkgs.rust-bin.stable.${verusToolchain}.default.override {
          extensions = [ "rustc-dev" "rust-src" "llvm-tools-preview" ];
        };

        # z3 built from source at the version Verus pins. Building from source
        # (rather than fetching a prebuilt z3 binary) keeps the whole toolchain
        # multi-platform and lets the proof run against the *exact* solver
        # version upstream tests against, so the `--no-cheating` proof check is
        # faithful to a stock Verus install.
        #
        # z3 4.12.5 predates gcc-15 and does not compile with it (a
        # `-Werror=template-body` regression in `static_matrix.h`). Pin an older
        # gcc stdenv that still builds it; the produced z3 binary is unaffected.
        z3 = (pkgs.z3.override { stdenv = pkgs.gcc13Stdenv; }).overrideAttrs (old: {
          version = z3Version;
          src = pkgs.fetchFromGitHub {
            owner = "Z3Prover";
            repo = "z3";
            rev = "z3-${z3Version}";
            hash = "sha256-Qj9w5s02OSMQ2qA7HG7xNqQGaUacA1d4zbOHynq5k+A=";
          };
        });

        # Offline cargo registry for the whole Verus workspace. importCargoLock
        # vendors crates.io deps content-addressed; the single git dependency
        # (utaal/getopts) needs its FOD hash supplied explicitly.
        cargoVendorDir = pkgs.rustPlatform.importCargoLock {
          lockFile = "${verusSrc}/source/Cargo.lock";
          outputHashes = {
            "getopts-0.2.21" = "sha256-N/QJvyOmLoU5TabrXi8i0a5s23ldeupmBUzP8waVOiU=";
          };
        };

        # vargo is Verus's cargo wrapper / build orchestrator. It has its OWN
        # Cargo.lock (a few crates not in the workspace lock, e.g. filetime),
        # so build it as a standalone rust package with its own vendored deps.
        # The resulting `vargo` binary then drives the main `vargo build`.
        vargo = pkgs.rustPlatform.buildRustPackage {
          pname = "vargo";
          version = verusVersion;
          # vargo's main.rs does `#[path = "../../common/consts.rs"]`, so it
          # needs the sibling `tools/common/` dir present — build from the whole
          # `tools` tree and point cargo at the `vargo` subdir.
          src = "${verusSrc}/tools";
          buildAndTestSubdir = "vargo";
          cargoRoot = "vargo"; # Cargo.lock lives in tools/vargo, not tools/
          cargoLock.lockFile = "${verusSrc}/tools/vargo/Cargo.lock";
          # vargo embeds hashes of its own source files at compile time; no
          # tests here (they require a full Verus checkout).
          doCheck = false;
        };

        # A minimal `rustup` shim. vargo (and the prebuilt launcher) shell out
        # to rustup to (a) discover the active toolchain and (b) run commands
        # under it. We have no rustup; instead we point everything at the
        # nix-provided `rustToolchain`. This implements exactly the three
        # subcommands vargo/the launcher use:
        #   - rustup show active-toolchain   (vargo: validate channel)
        #   - rustup toolchain list          (launcher)
        #   - rustup run <tc> -- <cmd...>    (vargo build + launcher)
        rustupShim = pkgs.writeShellScriptBin "rustup" ''
          tc="${verusToolchain}-${pkgs.stdenv.hostPlatform.rust.rustcTarget}"
          case "$1" in
            show)
              # `rustup show active-toolchain` -> "<tc> (overridden by ...)"
              echo "$tc (default)"
              ;;
            toolchain)
              # `rustup toolchain list`
              echo "$tc (default)"
              ;;
            run)
              shift            # drop 'run'
              shift            # drop toolchain name
              if [ "$1" = "--" ]; then shift; fi
              export LD_LIBRARY_PATH="${rustToolchain}/lib''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
              export RUSTC="${rustToolchain}/bin/rustc"
              exec "$@"
              ;;
            *)
              echo "verus-rustup-shim: unsupported subcommand: $@" >&2
              exit 1
              ;;
          esac
        '';

        verus = pkgs.stdenv.mkDerivation {
          pname = "verus";
          version = verusVersion;
          src = verusSrc;

          nativeBuildInputs = [
            rustToolchain
            rustupShim
            pkgs.makeWrapper
            pkgs.autoPatchelfHook
            pkgs.cmake # some workspace deps build native code via cmake
          ];
          buildInputs = [
            pkgs.stdenv.cc.cc.lib # libstdc++ / libgcc_s
            pkgs.zlib
          ];

          # The freshly built rust_verify is a rustc driver: autoPatchelfHook
          # cannot find librustc_driver-<hash>.so on its own (it lives in the
          # toolchain lib dir), so add it as an explicit runtime dependency.
          runtimeDependencies = [ rustToolchain ];

          # vargo orchestrates several `rustup run <tc> -- cargo build` steps.
          # Make cargo fully offline against the vendored registry.
          configurePhase = ''
            runHook preConfigure

            export HOME=$TMPDIR
            export CARGO_HOME=$TMPDIR/cargo-home
            mkdir -p $CARGO_HOME
            # Point cargo at the vendored registry (replaces crates.io and the
            # one git source) so the whole workspace builds offline.
            cat > $CARGO_HOME/config.toml <<EOF
            [source.crates-io]
            replace-with = "vendored-sources"

            [source."git+https://github.com/utaal/getopts.git?branch=parse-partial"]
            git = "https://github.com/utaal/getopts.git"
            branch = "parse-partial"
            replace-with = "vendored-sources"

            [source.vendored-sources]
            directory = "${cargoVendorDir}"
            EOF
            export CARGO_NET_OFFLINE=true

            # vargo wants z3 via VERUS_Z3_PATH (else it warns and the vstd
            # verification step fails). Point it at our from-source z3.
            export VERUS_Z3_PATH=${z3}/bin/z3

            # rustc-dev driver lives in the toolchain's lib dir.
            export LD_LIBRARY_PATH="${rustToolchain}/lib''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

            runHook postConfigure
          '';

          buildPhase = ''
            runHook preBuild

            cd source

            # vargo (built as its own rust package) drives the build.
            export PATH="${vargo}/bin:$PATH"

            # vargo build --release builds rust_verify, the support libs, the
            # `verus`/`cargo-verus` launchers, and verifies + compiles vstd
            # (this last step runs verus, hence needs z3). The default (no
            # --vstd-no-verify flag) verifies vstd, which is what we want.
            vargo build --release

            runHook postBuild
          '';

          installPhase = ''
            runHook preInstall

            # vargo lays the usable toolchain out under source/target-verus/release.
            artifacts=target-verus/release
            test -d "$artifacts" || { echo "ERROR: $artifacts not produced by vargo build" >&2; exit 1; }

            mkdir -p $out/verus
            cp -r "$artifacts"/. $out/verus/

            # Sanity: assert the rustc_driver the freshly built rust_verify links
            # against is provided by the pinned toolchain. Guards against a future
            # toolchain bump silently producing a broken binary.
            needed=$(patchelf --print-needed $out/verus/rust_verify 2>/dev/null | grep '^librustc_driver' || true)
            if [ -n "$needed" ] && [ ! -e "${rustToolchain}/lib/$needed" ]; then
              echo "ERROR: rust toolchain ${verusToolchain} does not provide $needed" >&2
              exit 1
            fi

            mkdir -p $out/bin

            # Pick the z3 vargo copied next to the binaries if present, else
            # fall back to our from-source z3.
            z3path=$out/verus/z3
            test -e "$z3path" || z3path=${z3}/bin/z3

            # Wrap the launchers: put the rustup shim on PATH and pin z3.
            makeWrapper $out/verus/verus $out/bin/verus \
              --prefix PATH : ${rustupShim}/bin \
              --set-default VERUS_Z3_PATH "$z3path"

            if [ -e $out/verus/cargo-verus ]; then
              makeWrapper $out/verus/cargo-verus $out/bin/cargo-verus \
                --prefix PATH : ${rustupShim}/bin \
                --set-default VERUS_Z3_PATH "$z3path"
            fi

            runHook postInstall
          '';

          meta = {
            description = "Verus: SMT-based verification of Rust (built from source ${verusVersion})";
            homepage = "https://github.com/verus-lang/verus";
            # Intentionally NOT restricted to x86_64-linux: this is a source
            # build, portable to any platform nixpkgs + rust-overlay support.
            platforms = pkgs.lib.platforms.unix;
          };
        };

        # `nix build .#quicksort` runs the actual verification as a derivation.
        # Verus runs rustc's lifetime/borrow check on proof code, which links,
        # so a C compiler must be on PATH. `--no-cheating` makes the build FAIL
        # if the source ever introduces an assume/admit/external_body.
        quicksort = pkgs.runCommand "verus-quicksort-verified"
          { nativeBuildInputs = [ pkgs.stdenv.cc ]; } ''
          cp ${./quicksort.rs} quicksort.rs
          ${verus}/bin/verus --no-cheating --triggers-mode silent quicksort.rs 2>&1 | tee $out
          grep -q "0 errors" $out
        '';
      in
      {
        packages = {
          inherit verus quicksort;
          default = verus;
        };

        devShells.default = pkgs.mkShell {
          packages = [ verus ];
        };
      });
}
