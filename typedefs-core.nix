{ build-idris-package
, contrib
, effects
, tparsec
, specdris
, bytes }:

build-idris-package {
  name = "typedefs-core";
  version = "dev";
  src = ./.;
  doCheck = true;

  idrisDeps = [
    contrib
    tparsec
    specdris
    bytes
    effects
  ];

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - library";
    homepage = "http://typedefs.com";
  };
}
