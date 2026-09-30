{
  description = "Ochr benchmark package: the toolchain for the Ochr checker (Lean 4 through elan) and the grader (Python 3)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        # `nix develop`, then `lake exe check` and `./grade.sh`.
        #
        # Lean comes through elan, which reads the pinned toolchain from ./lean-toolchain and
        # ./checker/lean-toolchain (leanprover/lean4:v4.33.0). make-sandbox.sh builds the
        # sandbox once, which installs that toolchain if it is missing, so a trial itself needs
        # no network. Python 3 runs grade.sh's checks.
        devShells.default = pkgs.mkShell {
          packages = [ pkgs.elan pkgs.python3 pkgs.git pkgs.coreutils ];
        };
      });
}
