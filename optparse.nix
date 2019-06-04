{ build-idris-package, fetchFromGitHub, lens, wl-pprint/*, lib*/}:
build-idris-package {
  name = "optparse";
  version = "2019-06-03";
  src = fetchFromGitHub {
    owner = "statebox";
    repo = "optparse-idris";
    rev = "bd5d52097f5f414be0f710f2a0cffb01a04e95fd";
    sha256 = "0nr0hgmndnwsd65r9g49zgkdqsryrzg3c86pv5w2q88ybxplm0ap"; # lib.fakeSha256; # This makes nix error out and give you the correct hash in stderr
  };
  idrisDeps = [ lens wl-pprint ];

  meta = {
    description = "Minimal port of optparse-applicative to idris";
    homepage = https://github.com/statebox/optparse-idris;
};
}
