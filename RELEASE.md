When releasing a new version of
[agda/cubical](https://github.com/agda/cubical), the following
procedure should be followed:

Release
=======
On the [releases page](https://github.com/agda/cubical/releases) of the cubical library's github page,
press the button `Draft a new release`.
Fill in the form with something like this:

* Title: version 0.X, compatible with Agda-X.X.X.X

* Description: Generate release notes

* Files: Download the current filetree via github (using the clone-button)
  Be carteful, this produces a zip which contains *a folder* which contains the filetree.
  Produce a good zip from that and a tar.gz named `cubical-0.X.zip` and `cubical-0.X.tar.gz`.

Post-release
============

* Increment the version number in the name field in the library file
  [cubical.agda-lib](cubical.agda-lib):

  ```diff
  -name: cubical-0.2
  +name: cubical-0.3
   include: .
   depend:
  ```

* Update README.md. There should be a new line in section "Compiling, using and installing`.

* Increment the `version` field in `flake.nix`.

* Update flake inputs by running `nix flake update`.
