{ stdenv, pkgs, idrisPackages }:

let
  build-idris-package = pkgs.callPackage ./.build-idris-package.nix {};
  tparsec = pkgs.callPackage ./.tparsec.nix {
    inherit build-idris-package;
  };
in

build-idris-package {
  name = "typedefs";
  version = "dev";
  src = ./.;
  doCheck = true;

  idrisDeps = with idrisPackages; [
    base
    contrib
    tparsec
    specdris
  ];

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - library";
    homepage = "http://typedefs.com";
  };
}
