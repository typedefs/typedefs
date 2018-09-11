{ stdenv, pkgs, idrisPackages }:

let
  build-idris-package = pkgs.callPackage ./.build-idris-package.nix {};
  tparsec = pkgs.callPackage ./.tparsec.nix {
    inherit build-idris-package;
  };
in

build-idris-package {
  name = "typedefs-parser-js";
  version = "dev";
  src = ./.;

  idrisDeps = with idrisPackages; [
    contrib
    tparsec
    js
  ];

  postInstall = ''
    install -D parser.js $out/share/typedefs/js/typedefs-parser.js
    install -D js/typedefs-parser.html $out/share/typedefs/js/typedefs-parser.html
  '';

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - parser - JavaScript";
    homepage = "http://typedefs.com";
  };
}
