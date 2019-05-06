{ stdenv, pkgs, idrisPackages }:

idrisPackages.build-idris-package {
  name = "typedefs";
  version = "dev";
  src = ./.;
  doCheck = true;

  idrisDeps = with idrisPackages; [
    contrib
    tparsec
    specdris
    bytes
  ];

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - library";
    homepage = "http://typedefs.com";
  };
}
