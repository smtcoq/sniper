{
  inputs = {
    SMTCoq.url = "github:SMTCoq/SMTCoq?ref=lafeychine/ci-tests";

    nixpkgs.follows = "SMTCoq/nixpkgs";
    flake-parts.follows = "SMTCoq/flake-parts";
  };

  outputs =
    inputs@{
      flake-parts,
      nixpkgs,
      self,
      SMTCoq,
      ...
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "aarch64-darwin"
        "x86_64-linux"
      ];

      flake = {
        lib = nixpkgs.lib.fix (lib: SMTCoq.lib // import ./nix/lib.nix { inherit lib; });

        overlays = {
          sniper = import ./nix/sniper;

          default = nixpkgs.lib.composeManyExtensions [
            SMTCoq.overlays.default
            self.overlays.sniper
          ];
        };
      };

      perSystem =
        {
          pkgs,
          system,
          ...
        }:
        {
          _module.args.pkgs = import nixpkgs {
            inherit system;
            overlays = [ self.overlays.default ];
          };

          formatter = pkgs.nixfmt-tree;

          packages = rec {
            inherit (pkgs.rocqPackages) sniper;

            default = sniper;
          };

          devShells.default = pkgs.mkShell {
            inputsFrom = [ pkgs.rocqPackages.sniper ];

            LFSCSIGS = "${pkgs.rocqPackages.smtcoq.passthru.lfsc-sigs}";
          };

          checks = pkgs.lib.listToAttrs (
            map (self.lib.mkSniper pkgs) (self.lib.mkRocqConstraints pkgs.rocqPackages "sniper")
          );
        };
    };
}
