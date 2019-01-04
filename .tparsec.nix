{ build-idris-package
, fetchFromGitHub
, lib
}:
build-idris-package  {
  name = "tparsec";
  version = "2018-07-24";

  ipkgName = "TParsec";

  src = fetchFromGitHub {
    owner = "gallais";
    repo = "idris-tparsec";
    rev = "6e8ff200e985243771b549905f1ba1547158af02";
    sha256 = "1cvm5pi8zd79jm1y1zw5nfk2gj0qrvsgd44gm6gsvmagf9irkc6p";
  };

  meta = {
    description = "TParsec - Total Parser Combinators in Idris";
    homepage = https://github.com/gallais/idris-tparsec;
    license = lib.licenses.gpl3;
    maintainers = [ lib.maintainers.brainrape ];
  };
}
