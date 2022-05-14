{
  description = "Cubical Agda";

  inputs.flake-utils.url = github:numtide/flake-utils;

  outputs = { self, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
    let pkgs = import nixpkgs { inherit system; };
        everythingFile = "./Everything.agda";
        extensions = [
          "agda"
          "agda-lib"
          "agdai"
          "lagda"
          "lagda.md"
          "lagda.org"
          "lagda.rst"
          "lagda.tex"
        ];
    in rec {
      packages.cubical = with pkgs;
        stdenv.mkDerivation {
          name = "cubical";
          src = ./.;
          LC_ALL = "en_US.UTF-8";
          preConfigure = ''export AGDA_EXEC=agda'';

          # The cubical library has several `Everything.agda` files, which are
          # compiled through the make file they provide.
          nativeBuildInputs = [ agda ghc glibcLocales ];

          installPhase = ''
            mkdir -p $out
            find -not \( -path ${everythingFile} \) -and \( ${lib.concatMapStringsSep " -or " (p: "-name '*.${p}'") extensions} \) -exec cp -p --parents -t "$out" {} +
          '';

        };
      defaultPackage = packages.cubical;
    });
}
