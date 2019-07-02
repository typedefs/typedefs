{ build-idris-package, fetchFromGitHub, lens, contrib /*, lib*/}:
build-idris-package {
  name = "optparse";
  version = "2019-07-02";
  src = fetchFromGitHub {
    owner = "statebox";
    repo = "optparse-idris";
    rev = "f5611b1c695299ff0d528cdfc53fd5c51b7fdd84";
    sha256 = "1r49476sds7sw5x0z0ya4h2xd2g23a0wx8in219j8ngkihcw10hn"; # lib.fakeSha256; # This makes nix error out and give you the correct hash in stderr
  };
  idrisDeps = [ lens contrib ];

  meta = {
    description = "Minimal port of optparse-applicative to idris";
    homepage = https://github.com/statebox/optparse-idris;
};
}
