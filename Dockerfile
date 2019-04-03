# This Dockerfile is experimental! It may or may not work for you.

# https://hub.docker.com/r/nixos/nix/
# TODO fix version to 2.1.1 (or whatever later one works)
FROM nixos/nix

# TODO unstable? hmm...
RUN nix-channel --add https://nixos.org/channels/nixpkgs-unstable nixpkgs
RUN nix-channel --update

WORKDIR /app

# TODO
# warning: there are multiple derivations named 'git-2.18.0'; using the first one
# installing 'git-2.18.0'
RUN nix-env -i git-2.18.0

# TODO install 'gnumake' via Nix?
RUN git clone https://github.com/typedefs/typedefs.git
# TODO spread out over 2 RUN commands? won't work b/c the cd won't have been done
RUN cd typedefs && nix-build
