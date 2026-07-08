{
  # Libraries
  mkRocqDerivation,

  # Dependencies
  stdlib,
  rocq-core,

  # Arguments
  version ? null,
}:

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

  defaultVersion = "v1.3.1-9.1";
  release."v1.3.1-9.1".sha256 = "sha256-LtYbAR3jt+JbYcqP+m1n3AZhAWSMIeOZtmdSJwg7L1A=";

  patchPhase = ''
    sed -i -e 's/(lang dune 3.13)/(lang dune 3.21)/g' dune-project
    sed -i -e 's/(using coq 0.8)/(using rocq 0.11)/g' dune-project
    sed -i -e 's/coq-core/rocq-runtime/g' src/dune
    sed -i -e 's/coq/rocq/g' examples/dune src/dune theories/dune theories/Prop/dune theories/Type/dune test-suite/dune
  '';
}
