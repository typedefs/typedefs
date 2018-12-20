{ stdenv, pkgs, idrisPackages }:

let
  typedefs = pkgs.callPackage ./typedefs.nix { };
in

idrisPackages.build-idris-package {
  name = "typedefs-examples";
  version = "dev";
  src = ./.;

  idrisDeps = with idrisPackages; [
    typedefs
  ];

  postInstall = ''
    install -D typedefs_examples $out/bin/typedefs-examples
  '';

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - examples";
    homepage = "http://typedefs.com";
  };
}
