{ stdenv, pkgs, idrisPackages }:

let
  build-idris-package = pkgs.callPackage ./.build-idris-package.nix {};
  name = "typedefs-examples";
in

build-idris-package {
  inherit name;
  ipkgName = name;
  version = "dev";
  src = ./.;

  idrisDeps = with idrisPackages; [
    contrib
    tparsec
  ];

  extraInstallPhase = ''
    install -D examples $out/bin/typedefs-examples
  '';

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - examples";
    homepage = "http://typedefs.com";
  };
}
