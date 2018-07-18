# Build an idris package
{ stdenv, lib, idrisPackages, gmp }:
  { idrisDeps ? []
  , noPrelude ? false
  , noBase ? false
  , name
  , version
  , ipkgName ? "*"
  , extraInstallPhase ? ""
  , extraBuildInputs ? []
  , ...
  }@attrs:
let
  allIdrisDeps = idrisDeps
    ++ lib.optional (!noPrelude) idrisPackages.prelude
    ++ lib.optional (!noBase) idrisPackages.base;
  idris-with-packages = idrisPackages.with-packages allIdrisDeps;
  newAttrs = builtins.removeAttrs attrs [
    "idrisDeps" "extraBuildInputs" "extraInstallPhase"
    "name" "version" "ipkgName" "noBase" "noPrelude"
  ] // {
    meta = attrs.meta // {
      platforms = attrs.meta.platforms or idrisPackages.idris.meta.platforms;
    };
  };
in
stdenv.mkDerivation ({
  name = "idris-${name}-${version}";

  buildInputs = [ idris-with-packages gmp ] ++ extraBuildInputs;
  propagatedBuildInputs = allIdrisDeps;

  # Some packages use the style
  # opts = -i ../../path/to/package
  # rather than the declarative pkgs attribute so we have to rewrite the path.
  postPatch = ''
    sed -i ${ipkgName}.ipkg -e "/^opts/ s|-i \\.\\./|-i ${idris-with-packages}/libs/|g"
  '';

  buildPhase = ''
    idris --build ${ipkgName}.ipkg
  '';

  checkPhase = ''
    if grep -q test ${ipkgName}.ipkg; then
      idris --testpkg ${ipkgName}.ipkg
    fi
  '';

  installPhase = ''
    idris --install ${ipkgName}.ipkg --ibcsubdir $out/libs
    IDRIS_DOC_PATH=$out/doc idris --installdoc ${ipkgName}.ipkg || true
    ${extraInstallPhase}
  '';

} // newAttrs)
