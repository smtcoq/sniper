{ lib }:

with lib;
{
  mkSniperName =
    {
      sniper,
      ...
    }@versions:
    "${mkSMTCoqName versions}-${mkFmt sniper.version}";

  mkSniperScope =
    pkgs:
    versions@{
      sniper,
      ...
    }:
    (mkSMTCoqScope pkgs versions).overrideScope (
      _: prev: {
        sniper = prev.sniper.override { version = sniper; };
      }
    );

  mkSniper =
    pkgs: versions:
    let
      rocqPackages = mkSniperScope pkgs versions;
    in
    {
      name = "sniper-${mkSniperName rocqPackages}";
      value = rocqPackages.sniper;
    };
}
