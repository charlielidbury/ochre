{
  description = "Low* in-place quicksort: F* + KaRaMeL (krml) -> C, pinned to dodge the --cmi version trap";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        # F* 2025.03.25 from nixpkgs. Crucially this is CACHED (no ~20min
        # source build) and still accepts `--cmi`, which KaRaMeL's krmllib
        # Makefile at the matched rev invokes. Newer F* renamed it to
        # --no_cmi and breaks the krmllib build (the documented version trap).
        fstar = pkgs.fstar;
        z3 = fstar.z3;

        # F* 2025.03.25 is built with OCaml 4.14.2, so use the matching set.
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;

        # KaRaMeL pinned to the commit just before F* 2025.03.25's tag
        # (2025-03-19), so its krmllib matches this F*'s ulib.
        karamelSrc = pkgs.fetchFromGitHub {
          owner = "FStarLang";
          repo = "karamel";
          rev = "25027047c3f0";
          hash = "sha256-Xgx1EpmP7aVLmiEY5pNc1Uoao1v0nBeTlEC3Sfodapk=";
        };

        karamel = pkgs.callPackage ./.nix/karamel.nix {
          inherit fstar ocamlPackages z3;
          src = karamelSrc;
          version = "25027047c3f0";
        };
      in {
        packages = {
          inherit karamel fstar;
          default = karamel;
        };

        devShells.default = pkgs.mkShell {
          packages = [ fstar karamel z3 pkgs.gcc pkgs.gnumake ];
          shellHook = ''
            export KRML_HOME=${karamel.home}
            export FSTAR_HOME=${fstar}
            echo "F*:    $(fstar.exe --version | head -1)"
            echo "krml:  $(krml -version 2>/dev/null | head -1 || echo present)"
            echo "KRML_HOME=$KRML_HOME"
          '';
        };
      });
}
