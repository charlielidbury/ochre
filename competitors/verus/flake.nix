{
  description = "Verus in-place quicksort competitor (SMT-backed verification of native Rust)";

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

        # Verus prebuilt release. The launcher (`verus`) requires a `rustup`
        # installation with the exact toolchain it was compiled against, because
        # `rust_verify` is a rustc driver that dlopens `librustc_driver-<hash>.so`
        # from that toolchain. We satisfy this WITHOUT rustup by:
        #   1. pinning the EXACT official stable rustc via rust-overlay (the
        #      `librustc_driver-6108105cd7e839cf.so` hash is bit-identical to the
        #      one Verus links against — verified at build time below), and
        #   2. shipping a tiny `rustup` shim that implements the only two
        #      sub-commands the launcher uses (`toolchain list` and
        #      `run <tc> -- <cmd>`), setting LD_LIBRARY_PATH to the toolchain libs.
        verusVersion = "0.2026.05.31.5dd6d83";
        verusToolchain = "1.95.0";

        rustToolchain = pkgs.rust-bin.stable.${verusToolchain}.default.override {
          extensions = [ "rustc-dev" "rust-src" "llvm-tools-preview" ];
        };

        verusSrc = pkgs.fetchurl {
          url = "https://github.com/verus-lang/verus/releases/download/release/${verusVersion}/verus-${verusVersion}-x86-linux.zip";
          hash = "sha256-0jQSHjhxiGDgDtqt0oByePcg+XFfjWyQ4i9dYGvpLPE=";
        };

        # The binaries we must patchelf so their ELF interpreter + rpath resolve
        # under Nix instead of /lib64 + a system rust toolchain.
        verusBins = [ "verus" "rust_verify" "z3" "cargo-verus" ];

        verus = pkgs.stdenv.mkDerivation {
          pname = "verus";
          version = verusVersion;
          src = verusSrc;

          nativeBuildInputs = [ pkgs.unzip pkgs.autoPatchelfHook pkgs.makeWrapper ];
          buildInputs = [
            rustToolchain
            pkgs.stdenv.cc.cc.lib # libgcc_s, libstdc++
            pkgs.zlib
          ];

          # autoPatchelfHook can't find librustc_driver (it lives in the rust
          # toolchain's lib dir, which we add explicitly via runtimeDependencies).
          runtimeDependencies = [ rustToolchain ];

          unpackPhase = ''
            unzip -q $src
            # The zip extracts to verus-x86-linux/
            sourceRoot=verus-x86-linux
          '';

          # autoPatchelfHook handles interpreter + rpath for all ELF files.
          dontConfigure = true;
          dontBuild = true;

          installPhase = ''
            runHook preInstall

            mkdir -p $out/verus
            cp -r . $out/verus

            # Assert the rustc_driver hash matches what verus links against. If a
            # future verus release bumps its rustc, this guard fails loudly rather
            # than producing a silently-broken devShell.
            needed=$(patchelf --print-needed $out/verus/rust_verify | grep '^librustc_driver' || true)
            if [ ! -e "${rustToolchain}/lib/$needed" ]; then
              echo "ERROR: rust toolchain ${verusToolchain} does not provide $needed" >&2
              echo "       (verus prebuilt and pinned rustc are out of sync)" >&2
              exit 1
            fi

            # rustup shim: the verus launcher shells out to `rustup`.
            mkdir -p $out/bin
            cat > $out/bin/rustup <<RUSTUP
            #!${pkgs.runtimeShell}
            case "\$1" in
              toolchain)
                # 'rustup toolchain list'
                echo "${verusToolchain}-x86_64-unknown-linux-gnu (default)"
                ;;
              run)
                # 'rustup run <toolchain> -- <cmd> <args...>'
                shift           # drop 'run'
                shift           # drop toolchain name
                if [ "\$1" = "--" ]; then shift; fi
                export LD_LIBRARY_PATH="${rustToolchain}/lib''${LD_LIBRARY_PATH:+:\$LD_LIBRARY_PATH}"
                export RUSTC="${rustToolchain}/bin/rustc"
                exec "\$@"
                ;;
              *)
                echo "verus-rustup-shim: unsupported subcommand: \$@" >&2
                exit 1
                ;;
            esac
            RUSTUP
            chmod +x $out/bin/rustup

            # Wrap `verus`: put our rustup shim first on PATH and point it at the
            # bundled z3. Users get a self-contained `verus` on PATH.
            makeWrapper $out/verus/verus $out/bin/verus \
              --prefix PATH : $out/bin \
              --set-default VERUS_Z3_PATH $out/verus/z3

            makeWrapper $out/verus/cargo-verus $out/bin/cargo-verus \
              --prefix PATH : $out/bin \
              --set-default VERUS_Z3_PATH $out/verus/z3

            runHook postInstall
          '';

          meta = {
            description = "Verus: SMT-based verification of Rust (prebuilt release ${verusVersion})";
            homepage = "https://github.com/verus-lang/verus";
            platforms = [ "x86_64-linux" ];
          };
        };

        # `nix build .#quicksort` runs the actual verification as a derivation.
        # Verus runs rustc's lifetime/borrow check on proof code, which links, so
        # a C compiler must be on PATH. `--no-cheating` makes the build FAIL if the
        # source ever introduces an assume/admit/external_body, guaranteeing the
        # result is a genuine machine-checked proof.
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
