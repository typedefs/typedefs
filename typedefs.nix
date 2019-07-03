{ build-idris-package, optparse, tparsec, bytes }:

build-idris-package {
  name = "typedefs";
  version = "dev";
  src = ./.;

  idrisDeps = [ optparse tparsec bytes ];

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - parser";
    homepage = "http://typedefs.com";
  };
}
