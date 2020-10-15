NAMING
======

This file provides a guide for how to name things. Note that many
files in the library do not currently follow these guidelines.

* First letter of structure names and types should be uppercase (like
  `Ring`) unless they represent properties (like `isProp`).

* Properties should start with `is`. These should be proved to be
  `isProp`'s.

* Use appropriate abbreviation, e.g.
  - `Comm` = commutative
  - `Assoc` = associative
  - `DistR`/`DistL` = distribute right/left

* Use camelCase as much as possible, also for properties/lemmas
  related to operations. For example: `+Assoc`, `·DistR+`.

* Results about `PathP` (path overs) should end with `P` (like
  `compPathP`).

- The order of terms in names should reflect the type and things
  should appear in the order the appear in the type (like
  `isContrUnit`). For functions things can either be separated by `→`
  (like `isProp→isSet`) or `To` (like `isoToEquiv`).
