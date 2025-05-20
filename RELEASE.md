When releasing a new version of
[agda/cubical](https://github.com/agda/cubical), the following
procedure should be followed:

Release
=======

Start by making a branch for the release. Change the following things:

* If needed, change the agda version used by the CI.

* If needed, Increment the `version` field in `flake.nix`.

* Update flake inputs by running `nix flake update`.

* Increment the version number in the name field in the library file
  [cubical.agda-lib](cubical.agda-lib):

  ```diff
  -name: cubical-0.2
  +name: cubical-0.3
   include: .
   depend:
  ```

* Update CITATION.cff with the new version and date of release.

* Update README.md. There should be a new line in section "Compiling, using and installing`.

On the [releases page](https://github.com/agda/cubical/releases) of the cubical library's github page,
press the button `Draft a new release`.
Fill in the form with something like this:

* Title: version 0.X, compatible with Agda-X.X.X(.X)

* Description: Generate release notes

* Files: Download the current filetree via github (using the clone-button)
  Be carteful, this produces a zip which contains a folder called ```cubical-master```.
  Produce a good zip from that and a tar.gz named `cubical-0.X.zip` and `cubical-0.X.tar.gz`,
  e.g. rename the folder to ```cubical``` and
  ```
  zip -r cubical-0.5.zip cubical
  tar cfz cubical-0.5.tar.gz cubical
  ```

Create and push a tag for the new version of the library.
