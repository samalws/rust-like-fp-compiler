{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  nativeBuildInputs = [ (pkgs.buildPackages.ghc.withPackages (p: with p; [transformers-either extra])) ];
}
