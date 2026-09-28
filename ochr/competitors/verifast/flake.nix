{
  description = "Examples from ochr/docs/00-idea.md done in separation logic with VeriFast";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        lib = pkgs.lib;
        verifast = pkgs.verifast;

        # Files VeriFast must accept. See README.md for what each one shows.
        accepted = [
          "addm" "addm-min" "concat"
          "concat-nospec-1" "concat-nospec-2" "concat-nospec-3"
          "concat-nospec-1-naive" "concat-nospec-1-classical"
          "add-nospec-1" "add-nospec-2"
        ];

        # Files VeriFast must reject, with the text its error must contain.
        rejected = {
          "concat-nospec-1-impostor-dropc" = "No matching heap chunks: lst(r,";
          "concat-nospec-1-impostor-swap" = "No matching heap chunks: lst(r,";
          "concat-nospec-1-impostor-head" = "No matching heap chunks: list_head_(r, _)";
          "concat-nospec-1-impostor-relink" = "No matching heap chunks: list_tail_(a, _)";
          "concat-nospec-1-impostor-swap23" = "No matching heap chunks: list_tail_(a, _)";
        };

        # Pure-spec files whose one lemma call, when deleted, must make VeriFast
        # reject them with the obligation it can then no longer discharge.
        withoutLemma = {
          addm = {
            lemmaCall = "//@ plus_zero(n);";
            obligation = "Cannot prove plus(n, Z) == n";
          };
          concat = {
            lemmaCall = "//@ app_assoc(xs, ys, zs);";
            obligation = "Cannot prove app(app(xs, ys), zs) == app(xs, app(ys, zs))";
          };
        };

        src = name: ./. + "/${name}.c";

        verifies = name:
          pkgs.runCommand "verifast-${name}" { nativeBuildInputs = [ verifast ]; } ''
            cp ${src name} ${name}.c
            verifast -shared ${name}.c | tee $out
          '';

        rejects = name: expected:
          pkgs.runCommand "verifast-${name}-rejected" { nativeBuildInputs = [ verifast ]; } ''
            cp ${src name} ${name}.c
            if verifast -shared ${name}.c > log 2>&1; then
              echo "expected VeriFast to reject ${name}.c" >&2; cat log >&2; exit 1
            fi
            grep -F '${expected}' log | tee $out
          '';

        rejectsWithoutLemma = name: ex:
          pkgs.runCommand "verifast-${name}-without-lemma" { nativeBuildInputs = [ verifast ]; } ''
            sed 's|${ex.lemmaCall}||' ${src name} > ${name}.c
            if verifast -shared ${name}.c > log 2>&1; then
              echo "expected verification of ${name}.c to fail without the lemma" >&2; cat log >&2; exit 1
            fi
            grep -F '${ex.obligation}' log | tee $out
          '';
      in {
        devShells.default = pkgs.mkShell { packages = [ verifast ]; };

        # `nix run` verifies every accepted file and prints VeriFast's reports.
        apps.default = {
          type = "app";
          program = toString (pkgs.writeShellScript "verify-examples" ''
            cd ${./.}
            for f in ${lib.concatMapStringsSep " " (n: "${n}.c") accepted}; do
              ${verifast}/bin/verifast -shared "$f" || exit 1
            done
          '');
        };

        checks =
          lib.genAttrs accepted verifies
          // lib.mapAttrs' (n: e: lib.nameValuePair "${n}-rejected" (rejects n e)) rejected
          // lib.mapAttrs' (n: e: lib.nameValuePair "${n}-without-lemma" (rejectsWithoutLemma n e)) withoutLemma;
      });
}
