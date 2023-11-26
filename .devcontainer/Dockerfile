FROM ocaml/opam

RUN opam install -y utop odoc ounit2 qcheck bisect_ppx menhir ocaml-lsp-server ocamlformat ocamlformat-rpc stdio

RUN sudo apt-get -y install htop

RUN opam install -y angstrom
