{
  description = "Idris 2 in-place quicksort competitor (QTT / linear mutable arrays)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [ pkgs.idris2 ];
        };

        # `nix build .#quicksort` — type-checks + builds the package via its
        # .ipkg (which declares the `contrib` dependency for Data.Linear.Array).
        packages.quicksort = pkgs.stdenv.mkDerivation {
          name = "idris-quicksort";
          src = ./.;
          nativeBuildInputs = [ pkgs.idris2 ];
          buildPhase = ''
            export HOME=$TMPDIR
            idris2 --build quicksort.ipkg
          '';
          installPhase = ''
            mkdir -p $out
            cp -r build $out/build
          '';
        };

        packages.default = self.packages.${system}.quicksort;
      });
}
