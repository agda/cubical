Core library for Cubical Agda
=============================

This folder contains the core library for Cubical Agda. It contains
the following things:

* Primitives: expose cubical agda primitives

* Prelude: basic cubical prelude

* Glue: definition of equivalences, Glue types and the univalence
  theorem

* PropositionalTruncation: Propositional truncation defined as a
  higher inductive type

* Id: Identity types and definitions of J, funExt, univalence and
  propositional truncation using Id instead of Path

* HoTT-UF: core library for HoTT/UF based on cubical type theory,
  where the cubical machinery is hidden, using the HoTT Book
  terminology and notation.


This library is intentionally kept as minimal as possible and should
not depend on the Agda standard library.
