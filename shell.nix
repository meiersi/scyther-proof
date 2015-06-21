{ pkgs ? (import <nixpkgs> {}) }:

(import ./default.nix) {
    stdenv          = pkgs.stdenv;

    # Install Nix from http://nixos.org/nix/
    # and call 'nix-shell' in the root directory of this project to drop into
    # a shell with exactly the right dependencies installed.

    # Here with a GHC 7.10.1
    haskellPackages = pkgs.haskell.packages.ghc7101;

    # Uncomment the following line to use GHC 7.8.4
    # haskellPackages = pkgs.haskell.packages.ghc784;
  }
