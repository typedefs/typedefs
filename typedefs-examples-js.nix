{ stdenv, pkgs, idrisPackages }:

let
  build-idris-package = pkgs.callPackage ./.build-idris-package.nix {};
in

build-idris-package {
  name = "typedefs-examples-js";
  version = "dev";
  src = ./.;

  idrisDeps = with idrisPackages; [
    contrib
    tparsec
    js
  ];

  postInstall = ''
    install -D examples.js $out/bin/typedefs-examples.js
  '';

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - examples";
    homepage = "http://typedefs.com";
  };
}
