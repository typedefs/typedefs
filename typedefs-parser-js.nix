{ stdenv, pkgs, idrisPackages }:

let
  typedefs = pkgs.callPackage ./typedefs.nix { };
in

idrisPackages.build-idris-package {
  name = "typedefs-parser-js";
  version = "dev";
  src = ./.;

  idrisDeps = with idrisPackages; [
    typedefs
    js
  ];

  postInstall = ''
    install -D typedefs_parser.js $out/share/typedefs/js/typedefs-parser.js
  '';

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - parser - JavaScript";
    homepage = "http://typedefs.com";
  };
}
