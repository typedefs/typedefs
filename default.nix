with import <nixpkgs> {};
with idrisPackages;
stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  src = ./src;
  buildInputs = [
    idris
    idrisPackages.contrib
  ];
}
