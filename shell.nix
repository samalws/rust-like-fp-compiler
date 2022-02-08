{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  nativeBuildInputs = [
    pkgs.hlint
    (pkgs.buildPackages.ghc.withPackages (p: with p; [
      transformers-either
      extra
      QuickCheck
      generic-arbitrary
      utility-ht
      parsec
      parsec-numbers
      ilist
    ]))
  ];
}
