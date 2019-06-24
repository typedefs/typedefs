{ build-idris-package, typedefs, js }:

build-idris-package {
  name = "typedefs-parser-js";
  version = "dev";
  src = ./.;

  idrisDeps = [ typedefs js ];

  postInstall = ''
    install -D typedefs_parser.js $out/share/typedefs/js/typedefs-parser.js
  '';

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - parser - JavaScript";
    homepage = "http://typedefs.com";
  };
}
