{ build-idris-package, typedefs-core }:

build-idris-package {
  name = "typedefs-examples";
  version = "dev";
  src = ./.;

  idrisDeps = [ typedefs-core ];

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - examples";
    homepage = "http://typedefs.com";
  };
}
