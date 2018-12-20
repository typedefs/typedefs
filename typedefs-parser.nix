{ stdenv, pkgs, idrisPackages }:

let
  typedefs = pkgs.callPackage ./typedefs.nix { };
in

idrisPackages.build-idris-package {
  name = "typedefs-parser";
  version = "dev";
  src = ./.;

  idrisDeps = with idrisPackages; [
    typedefs
  ];

  postInstall = ''
    install -D typedefs_parser $out/bin/typedefs-parser
  '';

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - parser";
    homepage = "http://typedefs.com";
  };
}
