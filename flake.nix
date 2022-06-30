{
  description = "Cubical Agda";

  inputs.flake-utils.url = github:numtide/flake-utils;

  outputs = { self, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
    let pkgs = import nixpkgs { inherit system; };
        cubical = with pkgs;
          agdaPackages.mkDerivation rec {
            pname = "cubical";
            version = "0.4";

            src = ./.;

            LC_ALL = "en_US.UTF-8";

            preConfigure = ''export AGDA_EXEC=agda'';

            # The cubical library has several `Everything.agda` files, which are
            # compiled through the make file they provide.
            nativeBuildInputs = [ ghc glibcLocales ];
            buildPhase = ''
              make
            '';
            meta = {};
          };
    in rec {
      packages.cubical = cubical;
      defaultPackage = cubical;
    });
}
