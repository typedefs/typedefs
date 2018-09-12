{ stdenv, pkgs, idrisPackages }:

let
  build-idris-package = pkgs.callPackage ./.build-idris-package.nix {};
  tparsec = pkgs.callPackage ./.tparsec.nix {
    inherit build-idris-package;
  };
in

build-idris-package {
  name = "typedefs-examples";
  version = "dev";
  src = ./.;

  idrisDeps = with idrisPackages; [
    contrib
    tparsec
    specdris
    js
  ];

  postInstall = ''
    install -D examples $out/bin/typedefs-examples
  '';

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - examples";
    homepage = "http://typedefs.com";
  };
}
