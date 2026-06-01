# Vendored from FStarLang/karamel@25027047c3f0 (.nix/karamel.nix), with the
# F* input wired to nixpkgs' fstar 2025.03.25 (which still accepts `--cmi`,
# matching this KaRaMeL rev's krmllib/Makefile). See ../NOTES.md.
{
  fstar,
  ocamlPackages,
  git,
  removeReferencesTo,
  src,
  stdenv,
  symlinks,
  version,
  which,
  z3,
}: let
  pname = "karamel";
  propagatedBuildInputs = with ocamlPackages; [
    batteries
    stdint
    ppx_deriving_yojson
    zarith
    pprint
    menhirLib
    sedlex
    process
    fix
    wasm
    ctypes
    visitors
    uucp
  ];
  nativeBuildInputs = [fstar git removeReferencesTo symlinks which z3] ++ (with ocamlPackages; [ocaml dune_3 findlib menhir]);
in
  stdenv.mkDerivation {
    inherit src version pname propagatedBuildInputs nativeBuildInputs;

    outputs = ["out" "home"];

    GIT_REV = version;

    # lib/KString.ml uses the stdlib `Str` module, but lib/dune (at this rev)
    # does not declare `str` as a dune library, so linking fails with
    # "No implementations provided ... Str". Add it explicitly.
    postPatch = ''
      substituteInPlace lib/dune --replace-fail "  unix" "  unix
  str"
    '';

    configurePhase = "export KRML_HOME=$(pwd)";

    enableParallelBuilding = true;

    # krmllib is KaRaMeL's *trusted* C support library. Re-verifying it with
    # this exact F* (2025.03.25) trips a postcondition proof in the unrelated
    # example module LowStar.Lib.AssocList. We don't depend on krmllib's
    # proofs (only its extracted C headers/runtime), so admit its SMT queries.
    # Our own quicksort is verified separately, fully, with no admits.
    OTHERFLAGS = "--admit_smt_queries true";

    preBuild = "mkdir -p krmllib/hints";

    preInstall = "export PREFIX=$out";
    postInstall = ''
      # OCaml leaves its full store path in produced binaries
      # Thus we remove every reference to it
      for binary in $out/bin/*
      do
        remove-references-to -t '${ocamlPackages.ocaml}' $binary
      done

      symlinks -c $KRML_HOME
      cp -r ./. $home
    '';

    dontFixup = true;
  }
