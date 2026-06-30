{
  description = "Idris2 dev shell with idris2-lsp";

  inputs = {
    # Pinned to the same rev as the repo-root flake so store paths / the
    # binary cache are shared (no duplicate nixpkgs eval, faster fetches).
    nixpkgs.url = "github:NixOS/nixpkgs/4bd9165a9165d7b5e33ae57f3eecbcb28fb231c9";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.idris2                       # the compiler (idris2-lsp shells out to it)
            pkgs.idris2Packages.idris2Lsp     # the language server (idris2-lsp on PATH)
          ];
        };
      });
}
