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
        "ghc910"
        "ghc912"
      ];

      haskellPackagesFor = pkgs: genAttrs supportedGhcs (ghc: pkgs.haskell.packages.${ghc})
        // { default = pkgs.haskell.packages.ghc910; };

      hoverlay = pkgs: hfinal: hprev: with pkgs.haskell.lib;
        (mapAttrs (pname: path: hfinal.callCabal2nix pname path { }) localPackages);

      haskellPackagesExtended = pkgs: mapAttrs
        (ghcVersion: haskellPackages: haskellPackages.override (_: {
          overrides = (hoverlay pkgs);
        }))
        (haskellPackagesFor pkgs);

      localPackagesFor = haskellPackages: mapAttrs (pname: _path: haskellPackages.${pname}) localPackages;
      allLocalPackagesFor = pkgs: ghcVersion: haskellPackages:
        pkgs.linkFarm "${projectName}-all-for-${ghcVersion}"
          (localPackagesFor haskellPackages);
    in
    flake-utils.lib.eachDefaultSystem
      (system:

        let
          pkgs = nixpkgs.legacyPackages.${system};
          forEachGHC = mapAttrs (allLocalPackagesFor pkgs) (haskellPackagesExtended pkgs);
          allGHCs = pkgs.linkFarm "${projectName}-all-ghcs" forEachGHC;
        in
        {
          # "packages" doesn't allow nested sets
          legacyPackages = mapAttrs
            (ghcVersion: haskellPackages: localPackagesFor haskellPackages // {
              "${projectName}-all" = allLocalPackagesFor pkgs ghcVersion haskellPackages;
            })
            (haskellPackagesExtended pkgs) // {
            "${projectName}-all" = forEachGHC;
          };

          packages = {
            default = allGHCs;
          };

          devShells = mapAttrs
            (ghcVersion: haskellPackages: haskellPackages.shellFor {
              packages = hps: attrValues (localPackagesFor haskellPackages);
              nativeBuildInputs = (
                lib.optional (versionAtLeast (haskellPackagesFor pkgs).${ghcVersion}.ghc.version "9.2")
                  (haskellPackagesFor pkgs).${ghcVersion}.haskell-language-server)
              ++ (with pkgs;
                [ cabal-install ]
              )
              ;
            })
            (haskellPackagesExtended pkgs);

          formatter = pkgs.nixpkgs-fmt;
        }) // {

      inherit supportedGhcs;
      inherit hoverlay;
    };
}
