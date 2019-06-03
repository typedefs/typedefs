{ build-idris-package, typedefs, optparse, }:

build-idris-package {
  name = "typedefs-parser";
  version = "dev";
  src = ./.;

  idrisDeps = [ typedefs optparse ];

  postInstall = ''
    install -D typedefs_parser $out/bin/typedefs-parser
  '';

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - parser";
    homepage = "http://typedefs.com";
  };
}
