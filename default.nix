{ stdenv, haskellPackages }:

let
  env = haskellPackages.ghcWithPackages (p: with p; [
    base
    array
    containers
    safe
    mtl
    cmdargs
    filepath
    directory
    process
    time
    parsec
    pretty
    tagsoup
    json
    uniplate
    utf8-string
  ]);
in
  stdenv.mkDerivation {
    name        = "scyther-proof";
    buildInputs = with haskellPackages; [env cabal-install alex];
    shellHook   = ''
      export NIX_GHC="${env}/bin/ghc"
      export NIX_GHCPKG="${env}/bin/ghc-pkg"
      export NIX_GHC_DOCDIR="${env}/share/doc/ghc/html"
      export NIX_GHC_LIBDIR=$( $NIX_GHC --print-libdir )
    '';
  }
