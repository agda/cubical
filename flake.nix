{
  description = "Cubical Agda";

  inputs.nixpkgs.url = "nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.flake-compat = {
    url = "github:edolstra/flake-compat";
    flake = false;
  };

  outputs = { self, flake-compat, flake-utils, nixpkgs }:
    let
      inherit (nixpkgs.lib) cleanSourceWith hasSuffix;
      overlay = final: prev: {
        cubical = final.agdaPackages.mkDerivation rec {
          pname = "cubical";
          version = "0.5";

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
      overlays = [ overlay ];
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
