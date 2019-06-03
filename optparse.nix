{ build-idris-package, fetchFromGitHub, lens, wl-pprint/*, lib*/}:
build-idris-package {
  name = "optparse";
  version = "2019-06-03";
  src = fetchFromGitHub {
    owner = "HuwCampbell";
    repo = "optparse-idris";
    rev = "0d8f9fac9e2c1c8f2fe7f983de1d46906ea38778";
    sha256 = "1djwjkc6z3qbz349znrzsi6jp2ai9nrzs97s2h3l8wq2h874zvl5"; # lib.fakeSha256; # This makes nix error out and give you the correct hash in stderr
  };
  idrisDeps = [ lens wl-pprint ];

  meta = {
    description = "Minimal port of optparse-applicative to idris";
    homepage = https://github.com/HuwCampbell/optparse-idris;
};
}
