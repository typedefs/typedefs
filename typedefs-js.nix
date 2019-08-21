{ build-idris-package, typedefs, tparsec, bytes, js, effects }:

build-idris-package {
  name = "typedefs-js";
  version = "dev";
  src = ./.;

  idrisDeps = [ tparsec bytes js effects ];

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - parser - JavaScript";
    homepage = "http://typedefs.com";
  };
}
