{
  # Libraries
  mkRocqDerivation,

  # Dependencies
  equations,

  # Arguments
  sha256 ? null,
  version ? "main",
}:

let
  version = "v1.4.1-9.1";
  release.${version}.sha256 = "sha256-tzoAWX74lg7pArGVP11QBvDRKMvmGxXvrf3+1E3Y4DI=";

  repo = "metarocq";
  owner = "MetaRocq";

  mlPlugin = true;

  utils = mkRocqDerivation rec {
    inherit mlPlugin release;
    inherit owner repo version;

    pname = "metarocq-utils";
    preBuild = "cd utils";
    propagatedBuildInputs = [ equations ];
  };

  common = mkRocqDerivation rec {
    inherit mlPlugin release;
    inherit owner repo version;

    pname = "metarocq-common";
    preBuild = "cd common";
    propagatedBuildInputs = [
      equations
      utils
    ];

    patchPhase = "patchShebangs ./configure.sh";
    configurePhase = "./configure.sh";
  };
in
mkRocqDerivation rec {
  inherit mlPlugin release;
  inherit owner repo version;

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
