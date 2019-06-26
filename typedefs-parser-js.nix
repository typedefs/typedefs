{ build-idris-package, typedefs, js }:

build-idris-package {
  name = "typedefs-parser-js";
  version = "dev";
  src = ./.;

  idrisDeps = [ typedefs js ];

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - parser - JavaScript";
    homepage = "http://typedefs.com";
  };
}
