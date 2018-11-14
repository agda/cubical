An experimental library for Cubical Agda
========================================

This library compiles with the master branch of Agda. To install Agda in
a cabal sandbox do:


```
git clone https://github.com/agda/agda
cd agda
cabal sandbox init
cabal install
```

The type theory that it implements is a variation of the cubical type
theory of:

[Cubical Type Theory: a constructive interpretation of the univalence
axiom](https://arxiv.org/abs/1611.02108) - Cyril Cohen, Thierry
Coquand, Simon Huber, Anders Mörtberg.


The key difference is that the Kan composition operations are
decomposed into homogeneous composition and generalized transport as
in:

[On Higher Inductive Types in Cubical Type
Theory](https://arxiv.org/abs/1802.01170) - Thierry Coquand, Simon
Huber, Anders Mörtberg

This makes it possible to directly represent higher inductive types.

The library is divided into:

* **Cubical/Core**: minimal core library to get Cubical Agda up and running.

* **Cubical/Basics**: basic theory (natural numbers, integers, basic
  results about equivalences...). This folder does not contain any HITs.

* **Cubical/HITs**: various higher inductive types and results about them.


Maintainers
-----------

* [Anders Mörtberg](http://www.cs.cmu.edu/~amoertbe/)

* [Andrea Vezzosi](http://www.cse.chalmers.se/~vezzosi/)
