{
  # Libraries
  lib,
  mkRocqDerivation,

  # Dependencies
  stdlib,
  rocq-core,

  # Arguments
  version ? null,
}:

let
  case = case: out: { inherit case out; };
in
mkRocqDerivation {
  inherit version;

  pname = "equations";
  owner = "mattam82";
  repo = "Coq-Equations";
  opam-name = "rocq-equations";

  propagatedBuildInputs = [
    stdlib
    rocq-core.ocamlPackages.ppx_optcomp
  ];

  mlPlugin = true;
  useDune = true;

  defaultVersion = lib.switch rocq-core.rocq-version [
    (case (lib.versions.isEq "9.2") "v1.3.2-9.2")
    (case (lib.versions.isEq "9.1") "v1.3.1-9.1")
    (case (lib.versions.isEq "9.0") "v1.3.1-9.0")
  ] null;

  release = {
    "v1.3.2-9.2".sha256 = "sha256-wpl6Uxy3M2xYuBZPLdsvkvBfXqzplHRrNjyePgLi2X4=";
    "v1.3.1-9.1".sha256 = "sha256-LtYbAR3jt+JbYcqP+m1n3AZhAWSMIeOZtmdSJwg7L1A=";
    "v1.3.1-9.0".sha256 = "sha256-186Z0/wCuGAjIvG1LoYBMPooaC6HmnKWowYXuR0y6bA=";
  };

  patchPhase = ''
    sed -i -e 's/(lang dune 3.13)/(lang dune 3.21)/g' dune-project
    sed -i -e 's/(using coq 0.8)/(using rocq 0.11)/g' dune-project
    sed -i -e 's/coq-core/rocq-runtime/g' src/dune
    find . -name "dune" -exec sed -i -e 's/coq/rocq/g' {} \;
  '';
}
