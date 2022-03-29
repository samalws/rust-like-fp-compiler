{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = [
    pkgs.nasm
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
