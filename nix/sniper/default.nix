let
  mkRocqPackages =
    base:
    base.overrideScope (
      final: _: {
        sniper = final.callPackage ./sniper.nix { };

        # NOTE: Remove these packages when they will be available upstream
        equations = final.callPackage ./equations.nix { };
        metarocq-template = final.callPackage ./metarocq-template.nix { };
      }
    );
in
final: prev: {
  rocqPackages = mkRocqPackages (prev.rocqPackages or { });

  rocqPackages_9_0 = mkRocqPackages (prev.rocqPackages_9_0 or { });
  rocqPackages_9_1 = mkRocqPackages (prev.rocqPackages_9_1 or { });
  rocqPackages_9_2 = mkRocqPackages (prev.rocqPackages_9_2 or { });
}
