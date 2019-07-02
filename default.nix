# Nix package for development
#
## INSTALL
#
# To build and install the packages in the user environment, use:
#
# $ nix-env -f . -i
#
## BUILD ONLY
#
# To build the packages and add it to the nix store, use:
#
# $ nix-build
#
## SHELL
#
# To launch a shell with all dependencies installed in the environment:
#
# $ nix-shell -A typedefs
#
# After entering nix-shell, build it:
#
# $ make
#
## NIXPKGS
#
# For all of the above commands, nixpkgs to use can be set the following way:
#
# a) by default it uses nixpkgs pinned to a known working version
#
# b) use the default nixpkgs from the system:
#    --arg pkgs 0
#
# c) use nixpkgs from an URL
#    --arg pkgs 0 -I nixpkgs=https://github.com/NixOS/nixpkgs/archive/18.09.tar.gz
#
# c) use nixpkgs at a given path
#    --arg pkgs /path/to/nixpkgs

{
 pkgs ? null,
}:

let
  config = {
    packageOverrides = pkgs: {
      idrisPackages = pkgs.idrisPackages.override {
        # We override the 'idrisPackages' packaget set
        # This means, that all these package definitions will 'see' eachother
        #  e.g. if typedefs-parser depends on typedefs, callPackage will automatically inject it
        # Add new idris packages to this list 
        overrides = idrisPackagesNew: idrisPackagesOld: {
          typedefs = idrisPackagesNew.callPackage ./typedefs.nix {};
          typedefs-parser = idrisPackagesNew.callPackage ./typedefs-parser.nix {};
          typedefs-parser-js = idrisPackagesNew.callPackage ./typedefs-parser-js.nix {};
          typedefs-examples = idrisPackagesNew.callPackage ./typedefs-examples.nix {};
          optparse = idrisPackagesNew.callPackage ./optparse.nix {};
        };
      };
    };
  };
  syspkgs = import <nixpkgs> { };
  pinpkgs = syspkgs.fetchFromGitHub {
    owner = "NixOS";
    repo = "nixpkgs";

    # binary cache exists for revisions listed in https://nixos.org/channels/
    rev = "c438c0e0b71c3b4be174486b0a5f60c67dd09721";
    sha256 = "014llk230q6871z73xzilvf93dna0q72y3y8hlgp47fc8h6fafim";
  };
  usepkgs = (
    if null == pkgs 
    then import pinpkgs
    else if 0 == pkgs 
    then import <nixpkgs>
    else import pkgs) { inherit config; };
  stdenv = usepkgs.stdenvAdapters.keepDebugInfo usepkgs.stdenv;

in {
  # This attribute set exposes what things will be built by a call to nix-build. See
  # its as the "CI" entrypoint.
  inherit (usepkgs.idrisPackages) 
    typedefs 
    typedefs-parser
    typedefs-parser-js 
    typedefs-examples;
}
