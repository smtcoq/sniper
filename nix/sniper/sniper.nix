{
  # Libraries
  lib,
  mkRocqDerivation,

  # Dependencies
  metarocq-template,
  smtcoq,
  rocq-core,

  # Arguments
  version ? null,
}:

mkRocqDerivation rec {
  inherit version;

  owner = "lafeychine";
  pname = "sniper";

  opam-name = "rocq-sniper";
  mlPlugin = true;
  useDune = true;

  defaultVersion = "dev";
  release."dev" = {
    src = lib.cleanSource ../..;
    hash = "";
  };

  propagatedBuildInputs = [
    metarocq-template
    smtcoq
  ];

  meta = {
    description = "A Rocq plugin for general proof automation";
    homepage = "https://github.com/smtcoq/sniper";
    license = lib.licenses.cecill-c;
  };
}
