Core library for Cubical Agda
=============================

This folder contains the core library for Cubical Agda. It contains
the following things:

* **Primitives**: exposes cubical agda primitives.

* **Glue**: definition of equivalences, Glue types and the univalence
  theorem.

* **Id**: identity types and definitions of J, funExt, univalence and
  propositional truncation using Id instead of Path.

This library is intentionally kept as minimal as possible and does not
depend on the Agda standard library.
