{
  # Libraries
  lib,
  mkRocqDerivation,

  # Dependencies
  rocq-core,
  stdlib,

  # Arguments
  version ? null,
}:

let
  case = case: out: { inherit case out; };
in
mkRocqDerivation rec {
  inherit version;

  owner = "rocq-community";
  pname = "coq-ext-lib";

  opam-name = "rocq-ext-lib";
  useDune = true;

  defaultVersion = lib.switch rocq-core.rocq-version [
    (case (lib.versions.isGe "9.1") "v0.13.1")
  ] null;

  release = {
    "v0.13.1".sha256 = "sha256-WJZaisQhbK9s/X4UeEYlhIaG2JqVWm1BiXzlDAcfEMk=";
  };

  propagatedBuildInputs = [
    stdlib
  ];

  patchPhase = ''
    sed -i -e 's/(lang dune 3.8)/(lang dune 3.21)/g' dune-project
    sed -i -e 's/(using coq 0.8)/(using rocq 0.11)/g' dune-project
    find . -name "dune" -exec sed -i -e 's/coq/rocq/g' {} \;
    sed -i -e 's/ (package rocq-ext-lib))/ (package rocq-ext-lib)\n (theories Stdlib))/' theories/dune
    mv coq-ext-lib.opam rocq-ext-lib.opam
  '';
}
