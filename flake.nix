{
  description = "nthese";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable-small";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    with builtins;
    with nixpkgs.lib;
    let
      inherit (nixpkgs) lib;
      projectName = "nthese";
      localPackages = {
        nthese = ./nthese;
      };

      # Always keep in sync with the tested-with section in the cabal file
      supportedGhcs = [
        "ghc96"
        "ghc98"
        "ghc910"
        "ghc912"
      ];

    in
    flake-utils.lib.eachDefaultSystem
      (system:

        let
          pkgs = nixpkgs.legacyPackages.${system};
          forEachGHC = mapAttrs (allLocalPackagesFor pkgs) (haskellPackagesExtended pkgs);
          allGHCs = pkgs.linkFarm "${projectName}-all-ghcs" forEachGHC;
          haskellPackagesPerGHC = genAttrs supportedGhcs (ghc: pkgs.haskell.packages.${ghc})
          // { default = pkgs.haskellPackages; };

          overrides = hfinal: hprev: with pkgs.haskell.lib;
            (mapAttrs (pname: path: hfinal.callCabal2nix pname path { }) localPackages);

          haskellPackagesExtended = mapAttrs
            (ghcVersion: haskellPackages: haskellPackages.override (_: {
              inherit overrides;
            }))
            haskellPackagesPerGHC;

          localPackagesFor = haskellPackages: mapAttrs (pname: _path: haskellPackages.${pname}) localPackages;
          allLocalPackagesFor = ghcVersion: haskellPackages:
            pkgs.linkFarm "${projectName}-all-for-${ghcVersion}"
              (localPackagesFor haskellPackages);
        in
        {
          # "packages" doesn't allow nested sets
          legacyPackages = mapAttrs
            (ghcVersion: haskellPackages: localPackagesFor haskellPackages // {
              "${projectName}-all" = allLocalPackagesFor ghcVersion haskellPackages;
            })
            haskellPackagesExtended // {
            "${projectName}-all" = forEachGHC;
          };

          packages = {
            default = allGHCs;
          } // mapAttrs allLocalPackagesFor haskellPackagesExtended;

          devShells = mapAttrs
            (ghcVersion: haskellPackages: haskellPackages.shellFor {
              packages = hps: attrValues (localPackagesFor haskellPackages);
              nativeBuildInputs = [
                haskellPackagesPerGHC.${ghcVersion}.haskell-language-server
              ]
              ++ (with pkgs;
                [ cabal-install ]
              )
              ;
            })
            haskellPackagesExtended;

          formatter = pkgs.nixpkgs-fmt;
        }) // {

      inherit supportedGhcs;
    };
}
