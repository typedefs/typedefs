{ build-idris-package, typedefs, tparsec, bytes, js }:

build-idris-package {
  name = "typedefs-js";
  version = "dev";
  src = ./.;

  idrisDeps = [ tparsec bytes js ];

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - parser - JavaScript";
    homepage = "http://typedefs.com";
  };
}
