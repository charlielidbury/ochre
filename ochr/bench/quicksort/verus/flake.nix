{
  description = "Verus toolchain for the ochr agent-effort benchmark (built from source, pinned)";

  # Verus built from source with its own build tool (vargo), pinned to the latest
  # Verus release as of 2026-09-30, with the Rust toolchain and z3 it pins.

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

        # Verus release/0.2026.09.27.3cf1832 (tagged 2026-09-27, the latest
        # non-rolling release on 2026-09-30). The short sha at the end of the
        # version string is the prefix of verusRev.
        verusVersion = "0.2026.09.27.3cf1832";
        verusRev = "3cf18325f0fd0c3040fbdec8c0f2255c0504c91a";
        verusToolchain = "1.98.1"; # upstream rust-toolchain.toml at verusRev
        z3Version = "4.16.0"; # upstream source/tools/get-z3.sh at verusRev

        verusSrc = pkgs.fetchFromGitHub {
          owner = "verus-lang";
          repo = "verus";
          rev = verusRev;
          hash = "sha256-IGbEVjZieWHsGvccwSwJMMzZEiyKAIivIZGkA4Z8o6M=";
        };

        # The exact stable toolchain Verus is pinned to, with the components
        # vargo needs to build rust_verify (a rustc driver).
        rustToolchain = pkgs.rust-bin.stable.${verusToolchain}.default.override {
          extensions = [ "rustc-dev" "rust-src" "llvm-tools-preview" ];
        };

        # z3 built from source at the version Verus pins.
        z3 = pkgs.z3.overrideAttrs (old: {
          version = z3Version;
          src = pkgs.fetchFromGitHub {
            owner = "Z3Prover";
            repo = "z3";
            rev = "z3-${z3Version}";
            hash = "sha256-DnhX3kxggnFmyYwXEPBsBA1rh4oor1oIJR5TMJk/jvc=";
          };
        });

        cargoVendorDir = pkgs.rustPlatform.importCargoLock {
          lockFile = "${verusSrc}/source/Cargo.lock";
          outputHashes = {
            "getopts-0.2.21" = "sha256-N/QJvyOmLoU5TabrXi8i0a5s23ldeupmBUzP8waVOiU=";
          };
        };

        vargo = pkgs.rustPlatform.buildRustPackage {
          pname = "vargo";
          version = verusVersion;
          # vargo's sources reach into ../../common and
          # ../../../source/cargo-verus-toolchains, so build from the repo root.
          src = verusSrc;
          buildAndTestSubdir = "tools/vargo";
          cargoRoot = "tools/vargo";
          cargoLock.lockFile = "${verusSrc}/tools/vargo/Cargo.lock";
          doCheck = false;
        };

        # A minimal `rustup` shim: vargo and the verus launcher shell out to
        # rustup to find and run the pinned toolchain.
        rustupShim = pkgs.writeShellScriptBin "rustup" ''
          tc="${verusToolchain}-${pkgs.stdenv.hostPlatform.rust.rustcTarget}"
          case "$1" in
            show) echo "$tc (default)" ;;
            toolchain) echo "$tc (default)" ;;
            which) shift; echo "${rustToolchain}/bin/$1" ;;
            run)
              shift; shift
              if [ "$1" = "--" ]; then shift; fi
              export LD_LIBRARY_PATH="${rustToolchain}/lib''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
              export RUSTC="${rustToolchain}/bin/rustc"
              exec "$@"
              ;;
            *) echo "rustup-shim: unsupported subcommand: $@" >&2; exit 1 ;;
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
            pkgs.cmake
          ];
          buildInputs = [ pkgs.stdenv.cc.cc.lib pkgs.zlib ];
          runtimeDependencies = [ rustToolchain ];

          # rust_verify's build script reads its version from `git`, which a
          # fetched source tree does not have. Hand it the pinned version instead.
          postPatch = ''
            substituteInPlace source/rust_verify/build.rs \
              --replace-fail 'get_verus_version(true).expect("version info")' \
                '(String::from("${verusVersion}"), String::from("${verusRev}"))' \
              --replace-fail 'get_git_head_paths().expect("Git HEAD paths")' \
                'Vec::<std::path::PathBuf>::new()'
          '';

          configurePhase = ''
            runHook preConfigure
            export HOME=$TMPDIR
            export CARGO_HOME=$TMPDIR/cargo-home
            mkdir -p $CARGO_HOME
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
            export VARGO_BUILD_VERSION=${verusVersion}
            export VARGO_BUILD_SHA=${verusRev}
            export VERUS_Z3_PATH=${z3}/bin/z3
            export LD_LIBRARY_PATH="${rustToolchain}/lib''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
            runHook postConfigure
          '';

          buildPhase = ''
            runHook preBuild
            cd source
            export PATH="${vargo}/bin:$PATH"
            # Builds rust_verify, the launchers, and verifies + compiles vstd.
            vargo build --release
            runHook postBuild
          '';

          installPhase = ''
            runHook preInstall
            artifacts=target-verus/release
            test -d "$artifacts" || { echo "ERROR: $artifacts not produced by vargo build" >&2; exit 1; }
            mkdir -p $out/verus
            cp -r "$artifacts"/. $out/verus/
            needed=$(patchelf --print-needed $out/verus/rust_verify 2>/dev/null | grep '^librustc_driver' || true)
            if [ -n "$needed" ] && [ ! -e "${rustToolchain}/lib/$needed" ]; then
              echo "ERROR: rust toolchain ${verusToolchain} does not provide $needed" >&2
              exit 1
            fi
            mkdir -p $out/bin
            z3path=$out/verus/z3
            test -e "$z3path" || z3path=${z3}/bin/z3
            # --compile links an executable, so a C toolchain goes on PATH too.
            makeWrapper $out/verus/verus $out/bin/verus \
              --prefix PATH : ${rustupShim}/bin:${pkgs.stdenv.cc}/bin \
              --set-default VERUS_Z3_PATH "$z3path"
            runHook postInstall
          '';

          meta = {
            description = "Verus ${verusVersion}, built from source";
            homepage = "https://github.com/verus-lang/verus";
            platforms = pkgs.lib.platforms.unix;
          };
        };
      in
      {
        packages = {
          inherit verus verusSrc;
          default = verus;
        };

        # `nix develop` gives `verus` (which compiles with its own pinned rustc),
        # a C toolchain for linking, and python3 for the grader.
        devShells.default = pkgs.mkShell {
          packages = [ verus pkgs.stdenv.cc pkgs.python3 ];
        };
      });
}
