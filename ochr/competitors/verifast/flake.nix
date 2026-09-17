{
  description = "The AddM / Add / AddZero example from ochr/docs/00-idea.md, done in separation logic with VeriFast";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        verifast = pkgs.verifast;
      in {
        devShells.default = pkgs.mkShell { packages = [ verifast ]; };

        # `nix run` verifies addm.c and prints VeriFast's report.
        apps.default = {
          type = "app";
          program = toString (pkgs.writeShellScript "verify-addm" ''
            cd ${./.}
            exec ${verifast}/bin/verifast -shared addm.c
          '');
        };

        checks = {
          # The example verifies.
          addm = pkgs.runCommand "verifast-addm" { nativeBuildInputs = [ verifast ]; } ''
            cp ${./addm.c} addm.c
            verifast -shared addm.c | tee $out
          '';

          # The counterfactual: without the pure lemma the same program is rejected,
          # with the obligation VeriFast cannot discharge named in the error.
          without-lemma = pkgs.runCommand "verifast-addm-without-lemma" { nativeBuildInputs = [ verifast ]; } ''
            sed 's|  //@ plus_zero(n);||' ${./addm.c} > addm.c
            if verifast -shared addm.c > log 2>&1; then
              echo "expected verification to fail without plus_zero" >&2; cat log >&2; exit 1
            fi
            grep -F 'Cannot prove plus(n, Z) == n' log | tee $out
          '';
        };
      });
}
