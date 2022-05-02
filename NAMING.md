NAMING
======

This file provides a guide for how to name things. Note that many
files in the library do not currently follow these guidelines.

* Use either descriptive names for universe levels or
  ```
  ℓ ℓ' ℓ'' ℓ''' ...
  ```

* Names of types should begin with an uppercase letter; names of
  non-type terms should begin with a lowercase letter. The exception
  is types that represent properties, which should begin with `is`
  (for example `isProp`).

* Use abbreviations to avoid very long names, e.g.
  - `Comm` = commutative
  - `Assoc` = associative
  - `DistR`/`DistL` = distribute right/left

* Use camelCase as much as possible, also for properties/lemmas
  related to operations. For example: `+Assoc`, `·DistR+`.

* Use Equiv or `≃` to refer to equivalences of types or structures.

* Use Iso or `≅` to refer to isomorphisms of types or structures.
  Here an isomorphism is a function with a quasi-inverse, i.e. a
  quasi-equivalence in the sense of the HoTT Book.

* Use `Path` or `≡` to refer to paths in names, not `Eq`, `Id`, or
  other "equality" or "identity"-related names.

* Results about `PathP` (path overs) should end with `P` (like
  `compPathP`).

* The order of terms in names should reflect the type and things
  should appear in the order they appear in the type (like
  `isContrUnit`). For functions things can either be separated by `→`
  (like `isProp→isSet`) or `To` (like `isoToEquiv`).

