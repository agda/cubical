{
  description = "Cubical Agda";

  inputs.nixpkgs.url = "nixpkgs/nixos-22.05";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
    let pkgs = nixpkgs.legacyPackages.${system};
        cubical = with pkgs;
          agdaPackages.mkDerivation rec {
            pname = "cubical";
            version = "0.4";

            src = pkgs.lib.cleanSourceWith {
              filter = name: type:
                !(pkgs.lib.hasSuffix ".nix" name)
              ;
              src = ./.;
            };


            LC_ALL = "C.UTF-8";

            preConfigure = ''export AGDA_EXEC=agda'';

            # The cubical library has several `Everything.agda` files, which are
            # compiled through the make file they provide.
            nativeBuildInputs = [ ghc ];
            buildPhase = ''
              make
            '';
            meta = {
              description = "An experimental library for Cubical Agda";
              homepage = "https://github.com/agda/cubical";
              license = "MIT License";
            };
          };
    in rec {
      packages = {
        cubical = cubical;
        agdaWithCubical = pkgs.agda.withPackages [cubical];
        default = cubical;
      };
    });
}
