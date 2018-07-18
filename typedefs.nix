{ stdenv, pkgs, idrisPackages }:

let
  build-idris-package = pkgs.callPackage ./.build-idris-package.nix {};
  name = "typedefs";
in

build-idris-package {
  inherit name;
  ipkgName = name;
  version = "dev";
  src = ./.;

  idrisDeps = with idrisPackages; [
    contrib
    idrisPackages.tparsec
  ];

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - library";
    homepage = "http://typedefs.com";
  };
}
