{
  # Libraries
  lib,
  mkRocqDerivation,

  # Dependencies
  equations,
  extlib,
  rocq-core,

  # Arguments
  sha256 ? null,
  version ? null,
}:

let
  case = case: out: { inherit case out; };

  defaultVersion = lib.switch rocq-core.rocq-version [
    (case (lib.versions.isEq "9.2") "v1.5.1-9.2")
    (case (lib.versions.isEq "9.1") "v1.5.1-9.1")
  ] null;

  release = {
    "v1.5.1-9.2".sha256 = "sha256-sinpbes0dEg2dGueu90ckY+qoyzeUS0uG6RrozHN86E=";
    "v1.5.1-9.1".sha256 = "sha256-0iFnSzfbufn2XhJ8EPyWu3KIiHYwxfMVQa2KT6GSR7s=";
  };

  repo = "metarocq";
  owner = "MetaRocq";

  mlPlugin = true;

  utils = mkRocqDerivation rec {
    inherit owner repo;
    inherit defaultVersion release;
    inherit mlPlugin version;

    pname = "metarocq-utils";
    preBuild = "cd utils";
    propagatedBuildInputs = [
      equations
      extlib
    ];
  };

  common = mkRocqDerivation rec {
    inherit owner repo;
    inherit defaultVersion release;
    inherit mlPlugin version;

    pname = "metarocq-common";
    preBuild = "cd common";
    propagatedBuildInputs = [
      equations
      extlib
      utils
    ];

    patchPhase = "patchShebangs ./configure.sh";
    configurePhase = "./configure.sh";
  };
in
mkRocqDerivation rec {
  inherit owner repo;
  inherit defaultVersion release;
  inherit mlPlugin version;

  pname = "metarocq-template-rocq";
  preBuild = "cd template-rocq";
  propagatedBuildInputs = [
    equations
    common
    utils
  ];

  patchPhase = ''
    patchShebangs ./configure.sh
    patchShebangs ./template-rocq/update_plugin.sh
    patchShebangs ./template-rocq/gen-src/to-lower.sh
    sed -i -e 's/mv $i $newi;/mv $i tmp; mv tmp $newi;/' ./template-rocq/gen-src/to-lower.sh
    sed -i -e 's/coq-core/rocq-runtime/g' template-rocq/META.rocq-metarocq-template-rocq
  '';
  configurePhase = "./configure.sh";
}
