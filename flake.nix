{
  description = "Cubical Agda";

  inputs.nixpkgs.url = "nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.flake-compat = {
    url = "github:edolstra/flake-compat";
    flake = false;
  };
  inputs.agda = {
    url = "github:agda/agda/v2.8.0";
    inputs = {
      nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, flake-compat, flake-utils, nixpkgs, agda }:
    let
      inherit (nixpkgs.lib) cleanSourceWith hasSuffix;

      # Required until the upstream agda overlay is fixed (https://github.com/agda/agda/issues/7755).
      # Afterwards, use agda.overlays.default instead.
      agdaOverlay = final: prev: {
        haskellPackages = prev.haskellPackages.override (old: {
          overrides = prev.lib.composeExtensions (old.overrides or (_: _: { }))
            (hfinal: hprev: {
              # The agda wrapper expects a separate bin output
              # (fixed in https://github.com/NixOS/nixpkgs/pull/424180/commits/ee74abc225)
              Agda = final.haskell.lib.enableSeparateBinOutput
                agda.packages.${prev.system}.default;
            });
        });
      };

      overlay = final: prev: {
        cubical = final.agdaPackages.mkDerivation rec {
          pname = "cubical";
          version = "0.9";

          src = cleanSourceWith {
            filter = name: type:
              !(hasSuffix ".nix" name)
            ;
            src = ./.;
          };


          LC_ALL = "C.UTF-8";

          # The cubical library has several `Everything.agda` files, which are
          # compiled through the make file they provide.
          nativeBuildInputs = [ final.ghc ];
          buildPhase = ''
            make
          '';
          meta = {
            description = "An experimental library for Cubical Agda";
            homepage = "https://github.com/agda/cubical";
            license = "MIT License";
          };
        };
        agdaWithCubical = final.agdaPackages.agda.withPackages [final.cubical];
      };

      overlays = [ agdaOverlay overlay ];
    in
    { overlays.default = overlay; } //
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = import nixpkgs { inherit system overlays; };
      in rec {
        packages = with pkgs; rec {
          inherit cubical agdaWithCubical;
          default = cubical;
        };
      });
}
