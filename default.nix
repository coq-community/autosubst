# This file was generated from `meta.yml`, please do not edit manually.
# Follow the instructions on https://github.com/coq-community/templates to regenerate.

{ pkgs ? (import <nixpkgs> {}), coq-version-or-url, shell ? false }:

let
  coq-version-parts = builtins.match "([0-9]+).([0-9]+)" coq-version-or-url;
  coqPackages =
    if coq-version-parts == null then
      pkgs.mkCoqPackages (import (fetchTarball coq-version-or-url) {})
    else
      pkgs."coqPackages_${builtins.concatStringsSep "_" coq-version-parts}";
in

with coqPackages;

pkgs.stdenv.mkDerivation {

  name = "autosubst";

  propagatedBuildInputs = [
    coq
  ];

  src = if shell then null else ./.;

  installFlags = "COQMF_COQLIB=$(out)/lib/coq/${coq.coq-version}/";
}
