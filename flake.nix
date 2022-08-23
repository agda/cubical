{
  description = "Cubical Agda";

  inputs.nixpkgs.url = "nixpkgs/nixos-22.05";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, flake-utils, nixpkgs }:
    let
      inherit (nixpkgs.lib) cleanSourceWith hasSuffix;
      overlay = final: prev: {
        cubical = final.agdaPackages.mkDerivation rec {
          pname = "cubical";
          version = "0.4";

          src = cleanSourceWith {
            filter = name: type:
              !(hasSuffix ".nix" name)
            ;
            src = ./.;
          };


          LC_ALL = "C.UTF-8";

          preConfigure = ''export AGDA_EXEC=agda'';

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
    in
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = import nixpkgs { inherit system; overlays = [ overlay ]; };
      in rec {
        packages = with pkgs; rec {
          inherit cubical agdaWithCubical;
          default = cubical;
        };
      });
}
