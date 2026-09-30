{
  description = "Agent-effort benchmark, aeneas condition: pinned Charon + Aeneas + Rust + elan";

  inputs = {
    # Aeneas main as of 2026-09-30. The Lean library the proofs import is the
    # `backends/lean` directory of THIS source tree (vendored by `setup.sh`), so
    # the translator and the library can never drift apart.
    aeneas.url = "github:AeneasVerif/aeneas/cd8fcc87dee884c499c4e99daeb184eb7efa1c85";
    # Charon is whatever this Aeneas pins (its `charon-pin` file and flake.lock
    # agree): Aeneas refuses LLBC from a mismatched Charon.
    charon.follows = "aeneas/charon";
    nixpkgs.follows = "aeneas/nixpkgs";
    flake-utils.follows = "aeneas/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, aeneas, charon }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        charonPkg = charon.packages.${system}.charon;
        aeneasPkg = aeneas.packages.${system}.aeneas;
        # The same nightly Charon drives rustc with, so `cargo test` and
        # `charon cargo` see one compiler.
        rustToolchain = charon.packages.${system}.rustToolchain;

        # Everything grade.sh needs, as one closure. make-sandbox.sh exposes
        # exactly this closure's bin/ to the assessed agent.
        tools = pkgs.buildEnv {
          name = "bench-aeneas-tools";
          paths = [
            charonPkg aeneasPkg rustToolchain
            pkgs.elan pkgs.python3 pkgs.git pkgs.coreutils pkgs.findutils
            pkgs.gnugrep pkgs.gnused pkgs.gawk pkgs.diffutils pkgs.bash
            pkgs.gnutar pkgs.gzip pkgs.curl pkgs.cacert
            pkgs.stdenv.cc  # the linker cargo test needs
          ];
        };

        # The part of the Aeneas source tree an assessed agent may see: the Lean
        # library, the docs, and the tutorial. NOT tests/ (it holds Aeneas's own
        # hashmap proofs, among others). setup.sh vendors this into vendor/aeneas.
        aeneas-src = pkgs.runCommand "aeneas-${aeneas.shortRev}-allowed-src" { } ''
          mkdir -p $out/backends $out/tutorial/lean $out/tutorial/src $out/docs
          cp -r ${aeneas}/backends/lean $out/backends/lean
          cp -r ${aeneas}/documentation $out/documentation
          cp -r ${aeneas}/docs/user $out/docs/user
          cp ${aeneas}/README.md ${aeneas}/LICENSE.md $out/
          cp -r ${aeneas}/tests/lean/Tutorial $out/tutorial/lean/Tutorial
          cp -r ${aeneas}/tests/src/tutorial $out/tutorial/src/tutorial
          echo "${aeneas.rev}" > $out/REV
        '';
        # Charon's documentation (what Rust it accepts, its limitations).
        charon-docs = pkgs.runCommand "charon-${charon.shortRev}-docs" { } ''
          mkdir -p $out
          cp -r ${charon}/docs/. $out/
          cp ${charon}/README.md ${charon}/LICENSE.md $out/
          echo "${charon.rev}" > $out/REV
        '';
      in {
        packages = {
          inherit tools aeneas-src charon-docs;
          default = tools;
        };
        devShells.default = pkgs.mkShell {
          packages = [ tools ];
          AENEAS_REV = aeneas.rev;
          CHARON_REV = charon.rev;
        };
      });
}
