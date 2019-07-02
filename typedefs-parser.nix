{ build-idris-package, typedefs, optparse }:

build-idris-package {
  name = "typedefs-parser";
  version = "dev";
  src = ./.;

  idrisDeps = [ typedefs optparse ];

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - parser";
    homepage = "http://typedefs.com";
  };
}
