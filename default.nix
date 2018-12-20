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
#    --arg pkgs 0 -I nixpkgs=https://github.com/NixOS/nixpkgs/archive/18.03.tar.gz
#
# c) use nixpkgs at a given path
#    --arg pkgs /path/to/nixpkgs

{
 pkgs ? null,
}:

let
  syspkgs = import <nixpkgs> { };
  pinpkgs = syspkgs.fetchFromGitHub {
    owner = "NixOS";
    repo = "nixpkgs";

    # binary cache exists for revisions listed in https://nixos.org/channels/
    rev = "eaeb20dd09f1311dc6a55c2e47777d89ac93e8a9"; # https://nixos.org/channels/nixpkgs-unstable/git-revision
    sha256 = "1f1zwgsf5x5k1achi0nwymmwfx96lhjjc6hs1j6ibh8182imvvfv";
  };
  usepkgs = if null == pkgs then
             import pinpkgs {}
            else
              if 0 == pkgs then
                import <nixpkgs> { }
              else
                import pkgs {};
  stdenv = usepkgs.stdenvAdapters.keepDebugInfo usepkgs.stdenv;

in {
  typedefs = usepkgs.callPackage ./typedefs.nix {};
  typedefs-parser = usepkgs.callPackage ./typedefs-parser.nix {};
  typedefs-parser-js = usepkgs.callPackage ./typedefs-parser-js.nix {};
  typedefs-examples = usepkgs.callPackage ./typedefs-examples.nix {};

}
