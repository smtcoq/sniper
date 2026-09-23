{
  # Libraries
  lib,
  mkRocqDerivation,

  # Dependencies
  metarocq-template,
  smtcoq,
  rocq-core,
  rocq-elpi,

  # Arguments
  version ? null,
}:

let
  case = case: out: { inherit case out; };
in
mkRocqDerivation rec {
  inherit version;

  owner = "lafeychine";
  pname = "sniper";

  opam-name = "rocq-sniper";
  mlPlugin = true;
  useDune = true;

  defaultVersion = lib.switch rocq-elpi.version [
    (case (lib.versions.isGe "3.3.1") "dev")
  ] null;
  release."dev" = {
    src = lib.cleanSource ../..;
    hash = "";
  };

  propagatedBuildInputs = [
    metarocq-template
    smtcoq
  ];

  doCheck = true;
  checkPhase = ''
    runHook preCheck
    dune runtest -p ${opam-name} ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
    runHook postCheck
  '';

  meta = {
    description = "A Rocq plugin for general proof automation";
    homepage = "https://github.com/smtcoq/sniper";
    license = lib.licenses.cecill-c;
  };
}
