When releasing a new version of
[agda/cubical](https://github.com/agda/cubical), the following
procedure should be followed:

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
