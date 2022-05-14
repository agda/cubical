{
  description = "Cubical Agda";

  inputs.flake-utils.url = github:numtide/flake-utils;

  outputs = { self, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
    let pkgs = import nixpkgs { inherit system; };
    in rec {
      packages.cubical = with pkgs;
        stdenv.mkDerivation {
          name = "cubical";
          src = ./.;
          LC_ALL = "en_US.UTF-8";

          # The cubical library has several `Everything.agda` files, which are
          # compiled through the make file they provide.
          nativeBuildInputs = [ agda ghc glibcLocales ];
          install = "touch $out";
        };
      defaultPackage = packages.cubical;
    });
}
