Core library for Cubical Agda
=============================

This folder contains the core library for Cubical Agda. It contains
the following things:

* **Primitives**: exposes cubical agda primitives.

* **Prelude**: basic cubical prelude.

* **Glue**: definition of equivalences, Glue types and the univalence
  theorem.

* **PropositionalTruncation**: propositional truncation defined as a
  higher inductive type.

* **Id**: identity types and definitions of J, funExt, univalence and
  propositional truncation using Id instead of Path.

* **HoTT-UF**: core library for HoTT/UF based on cubical type theory,
  where the cubical machinery is hidden, using the HoTT Book
  terminology and notations.


This library is intentionally kept as minimal as possible and does not
depend on the Agda standard library.
